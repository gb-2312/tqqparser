package main

import (
	"bufio"
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// 定义常量
const (
	NORMAL_SLASHES     = "/"
	MINUS_SIGN         = "-"
	DEFAULT_CHARSET    = "utf-8"
	ZERO               = 0
	ERROR              = -1
	NOT_FOUND          = ERROR
	EMPTY_STR          = ""
	NEXT_LINE_CHAR     = '\n'
	QUESTION_STR       = "?"
	DOT_STR            = "."
	HTTP_PREFIX        = "http://"
	WINDOWS_OS_SLASHES = "\\"
	EQUAL_SIGN         = "="
	HASH_SIGN          = "#"

	DEFAULT_PAGE_NUMBER         = 1
	DEFAULT_TOPIC_ID            = "500000000000000"
	DEFAULT_MAX_RETRY_COUNT     = 20
	DEFAULT_RETRY_SLEEP_SECONDS = time.Second * 2
	DEFAULT_USER_AGENT          = "Mozilla/5.0 (Linux; Android 5.0; SM-G900P Build/LRX21T) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/65.0.3325.181 Mobile Safari/537.36"

	DEFAULT_HTML_TEMPLATE       = "<!DOCTYPE html><html><head></head><body>%s</body></html>"
	CHECK_API_URI               = "http://api.t.qq.com/asyn/index.php?&time=%s&page=%s&id=%s&isrecom=0&u=%s&apiType=14&apiHost=%s&_r=%s&g_tk=%s"
	API_HOST                    = "http%3A%2F%2Fapi.t.qq.com"
	REFERENCE_PAGE_URL_TEMPLATE = "http://t.qq.com/%s?preview"

	WRITE_FILE_TIPS                          = "正在写入文件:%s\n"
	RETRY_FETCH_TIPS                         = "第%d次, 允许再次重试...\n"
	RETRY_TOO_MANY_TIPS                      = "重试次数过多!"
	PAGE_CONTENT_EMPTY_TIPS                  = "page.content内容为空!"
	PAGE_ITEM_ARR_EMPTY_TIPS                 = "page_item_arr为空! 可能已经抓取完数据."
	GEN_JSON_CONTENT_OF_PAGE_ITEM_EMPTY_TIPS = "genJsonContent::page_items为空!"
	GEN_HTML_CONTENT_OF_PAGE_ITEM_EMPTY_TIPS = "getHtmlContent::page_items为空!"
	PARSER_ALREADY_INITED_TIPS               = "ALREADY INIT !"
	POST_BODY_NIL_TIPS                       = "body NIL!"
	PARSE_MATCH_FIND_RESULT_NIL_TIPS         = "find_result NIL!"
	CNF_FILE_EXISTS_TIPS                     = "请确认是否已经存在设定: settings.cnf?"
	CNF_FILE_WAS_RIGHT_TIPS                  = "请确认是否已经正确设定配置数值: settings.cnf?"
	CNF_FORMAT_ERROR_TIPS                    = "设置的数值格式错误:%T \n"
	FILE_ALREADY_EXISTS_TIPS_TIPS            = "文件已经存在: %s"
	DEFAULT_SETTINGS_CNF_PATH                = "./settings.cnf"
	MEDIA_FOLDER_NAME                        = "multimedia"
	PICTURE_SAVING_SIZE                      = "2000"
)

// 定义变量
var (
	// 默认请求的headers信息
	DEFAULT_REQUEST_HEADERS = map[string]string{
		"Accept-Language": "zh-CN,zh; q = 0.9, en; q =0.8",
		"Accept":          "* /*",
		"User-Agent":      DEFAULT_USER_AGENT,
		"Referer":         "http://api1.t.qq.com/proxy.html",
		"Connection":      "keep-alive",
	}
	// only-once
	once sync.Once
	// 配置文件
	cnf *Config
	// 默认导出的数据类型
	DEFAULT_DATA_TYPE = HTML
)

// Method-Type
type MethodType string

// 定义常用的HTTP_METHOD类型
const (
	//GET
	GET MethodType = "GET"
	// POST
	POST MethodType = "POST"
)

// 数据类型
type DataType string

// 定义常用的数据类型
const (
	// JSON
	JSON DataType = "JSON"
	// HTML
	HTML DataType = "HTML"
)

// 兼容postSimpleReq函数
// @param method_type MethodType
// @param request_url POST请求地址
// @param params 请求参数字典
// @param cookies 所有的cookies
// @return <body内容, []cookie, error>
type HttpClient func(method_type MethodType, request_url string,
	params map[string]string, cookies []*http.Cookie) ([]byte, []*http.Cookie, error)

// parser抽象
type Parser interface {
	// 初始化
	Initial()

	// 销毁
	Destroy()

	// (protected方法)post请求
	// post(Call:: HttpClient.func())
	// @param method_type MethodType
	// @param request_url POST请求地址
	// @param params 请求参数字典
	// @param cookies 所有的cookie
	// @return <body内容, error>
	post(method_type MethodType, request_url string,
		params map[string]string, cookies []*http.Cookie) ([]byte, error)

	// 解析, 提取关键的数据源
	GetData()

	// 解析response_body, 正则提取正确的数据
	// @param body 源数据内容
	// @return 提取到的正确数据源字符串
	parse(body []byte)

	// 数据写入到本地磁盘
	// @param data_type 数据类型
	WriteData(data_type DataType)
}

// 可以Append的Buf
type AppendBuf struct {
	byteBuf *bytes.Buffer
}

// append-method
// @param val append value
// @return *AppendBuf(self)
func (buf *AppendBuf) append(val string) *AppendBuf {
	buf.byteBuf.WriteString(val)
	return buf
}

// reset
func (buf *AppendBuf) Reset() {
	buf.byteBuf.Reset()
}

// toString()
// @return .String()
func (buf *AppendBuf) String() string {
	return buf.byteBuf.String()
}

// 当前要请求的页面所需的uri参数
type Page struct {
	// 页码
	pageNumber int
	// 与分页相关: 上一个承上启下的TopicId
	lastTopicId string
	// 与分页相关: 上一个承上启下的TopicTimestamp
	lastTimestamp int
	// 抓取的结果
	content string
	// 临时的引用item单元的字符串临时缓冲区
	tempSourceHtmlItemBuf *AppendBuf
	// 定义读取item单元的字符串临时缓冲区
	tempHtmlItemBuf *AppendBuf
	// 渲染html的字符串缓冲区
	htmlBuf *AppendBuf
}

// pageNumber += 1
func (page *Page) incPageNumber() {
	page.pageNumber++
}

// 更新 `lastTopicId`, `lastTimestamp`
// @param lastTopicId 上一个承上启下的TopicId
// @param lastTimestamp 上一个承上启下的TopicTimestamp
func (page *Page) update(lastTopicId string, lastTimestamp int) {
	page.lastTopicId = lastTopicId
	page.lastTimestamp = lastTimestamp
}

// 获取当前Page构造的完整请求URL
// @return 完整的url
func (page *Page) getPageUrl() string {
	return fmt.Sprintf(CHECK_API_URI, int2String(page.lastTimestamp), int2String(page.pageNumber),
		page.lastTopicId, cnf.dict.GetStr("USERNAME"), API_HOST,
		getRandomNumber(), cnf.dict.GetStr("GLOBAL_TOKEN"))
}

// 反编排content为[]PageItem的格式(用于解析html页码)
// @return 反编排为*[]PageItem
func (page *Page) unmarshalItems() []PageItem {
	if page.content == "" {
		log.Fatal(PAGE_CONTENT_EMPTY_TIPS)
		return nil
	}

	var page_item_arr []PageItem
	err := json.Unmarshal([]byte(page.content), &page_item_arr)
	if err != nil {
		log.Fatal(err)
		return nil
	}

	if page_item_arr != nil {
		if len(page_item_arr) <= 0 {
			panic(PAGE_ITEM_ARR_EMPTY_TIPS)
		}
		last_item := page_item_arr[len(page_item_arr)-1]
		page.update(last_item.Id, last_item.Timestamp)
	}

	return page_item_arr
}

// item单元, 渲染为html标签
// @param item 当前的PageItem
// @return 渲染后的html标签字符串
func (page *Page) getHtmlItem(item PageItem) string {
	var currentBuf *AppendBuf
	if item.wasQuoted {
		currentBuf = page.tempSourceHtmlItemBuf
		currentBuf.append("<strong style='color: red'>")
	} else {
		currentBuf = page.tempHtmlItemBuf
	}
	currentBuf.Reset()
	//
	currentBuf.append(item.Nick).append("(").append(item.Name).append("): <article>").
		append(item.Content).append("</article><br />")
	//
	if item.Image != nil {
		for _, unit := range item.Image {
			pic_url := unit + NORMAL_SLASHES + PICTURE_SAVING_SIZE
			saving_path := getMediaFolder() + getOsSlashes() + getImgName(unit)
			checkAndWriteMedia(getMediaFolder(), saving_path, pic_url)
			currentBuf.append("<img src='").append(pic_url).append("' /><br />")
		}
	}
	//
	if item.Videos != nil {
		for _, unit := range item.Videos {
			currentBuf.append("<a href='").append(unit.RealUrl).append(" title='").
				append(unit.Title).append("'><img src='").append(unit.MiniPicUrl).
				append("' /></a><br />")
		}
	}
	if item.Source != nil {
		item.Source.wasQuoted = true
		source_item := page.getHtmlItem(*item.Source)
		if source_item != EMPTY_STR {
			currentBuf.append(source_item)
		}
	}
	currentBuf.append(item.From).append("<br />")
	currentBuf.append("<a href='http://t.qq.com/p/t/").append(item.Id).
		append("'>").append(item.Time).append("</a><hr color='red' />\n")
	//
	if item.wasQuoted {
		currentBuf.append("</strong>")
	}
	return currentBuf.String()
}

// 根据pic_url获取图片名称
// @param pic_url 图片资源地址(不包含大小/2000)
// @return 实际保存的完整文件名称
func getImgName(unit string) string {
	return unit[strings.LastIndex(unit, NORMAL_SLASHES) : len(unit)-1]
}

// 获取json格式的内容
// @return json-data
func (page *Page) genJsonContent() string {
	page_items := page.unmarshalItems()
	if page_items == nil {
		log.Fatal(GEN_JSON_CONTENT_OF_PAGE_ITEM_EMPTY_TIPS)
		return EMPTY_STR
	}

	return page.content
}

// 生成`整体的html标签内容`
func (page *Page) genHtmlContent() string {
	defer page.htmlBuf.Reset()
	page_items := page.unmarshalItems()
	if page_items == nil {
		log.Fatal(GEN_HTML_CONTENT_OF_PAGE_ITEM_EMPTY_TIPS)
		return EMPTY_STR
	}

	// 渲染简易丑陋的html模板
	for _, item := range page_items {
		page.htmlBuf.append(page.getHtmlItem(item))
	}

	return fmt.Sprintf(DEFAULT_HTML_TEMPLATE, page.htmlBuf.String())
}

// 视频的item
type VideoItem struct {
	RealUrl    string `json:"real_url"`
	Title      string `json:"title"`
	MiniPicUrl string `json:"mini_pic_url"`
}

// 每条微博item信息
type PageItem struct {
	Nick      string      `json:"nick"`
	Name      string      `json:"name"`
	Content   string      `json:"content"`
	Image     []string    `json:"image"`
	Videos    []VideoItem `json:"videos"`
	Source    *PageItem   `json:"source"`
	From      string      `json:"from"`
	Id        string      `json:"id"`
	Timestamp int         `json:"timestamp"`
	Time      string      `json:"time"`
	// 自定义: 是否属于引用关系
	wasQuoted bool
}

// t.qq.com parser
type TQQParser struct {
	// 实现Parser
	Parser
	// HttpClient-adapter
	client HttpClient
	// cookies
	cookies []*http.Cookie
	// 绑定的当前page
	page *Page
}

func (parser *TQQParser) Initial() {
	if parser.client != nil || parser.page != nil {
		log.Fatal(PARSER_ALREADY_INITED_TIPS)
		return
	}

	parser.client = postSimpleReq
	parser.page = &Page{DEFAULT_PAGE_NUMBER, DEFAULT_TOPIC_ID,
		int(time.Now().UnixNano()), EMPTY_STR,
		&AppendBuf{new(bytes.Buffer)},
		&AppendBuf{new(bytes.Buffer)},
		&AppendBuf{new(bytes.Buffer)}}

}

func (parser *TQQParser) Destroy() {
	parser.Parser = nil
	parser.client = nil
	parser.cookies = nil
	parser.page = nil
}

func (parser *TQQParser) post(method_type MethodType, request_url string,
	params map[string]string, cookies []*http.Cookie) ([]byte, error) {
	body, new_cookie, err := parser.client(method_type, request_url, params, cookies)
	if err == nil && new_cookie != nil {
		// update-cookie
		parser.cookies = new_cookie
	}

	return body, err
}

func (parser *TQQParser) GetData() {
	body, err := parser.post(POST, parser.page.getPageUrl(), nil, parser.cookies)
	if err != nil {
		log.Fatal(err)
		return
	}

	if body == nil {
		log.Fatal(POST_BODY_NIL_TIPS)
		return
	}

	parser.parse(body)
}

func (parser *TQQParser) parse(body []byte) {
	reg := regexp.MustCompile("{result:.*?,'talk':(.*?), 'noSign':(.*?)")
	find_result := reg.FindStringSubmatch(string(reg.Find(body)))
	if find_result == nil {
		log.Fatal(PARSE_MATCH_FIND_RESULT_NIL_TIPS)
		return
	}

	content := find_result[1]
	parser.page.content = content
}

func (parser *TQQParser) WriteData(data_type DataType) {
	content := EMPTY_STR
	switch data_type {
	case JSON:
		content = parser.page.genJsonContent()
		break
	case HTML:
		content = parser.page.genHtmlContent()
		break
	default:
		return
	}

	if content == EMPTY_STR {
		return
	}

	folder_path := getSavingRootFolder()
	file_path := folder_path + getOsSlashes() + int2String(parser.page.pageNumber) + DOT_STR + string(data_type)

	checkAndWriteData(folder_path, file_path, content)

	// if success, than page-number +1
	parser.page.incPageNumber()
}

// 检查 AND 写入为Data文件
// @param folder_path 保存的目录
// @param file_path 文件保存位置
// @param content 文件写入内容
func checkAndWriteData(folder_path string, file_path string, content string) {
	checkFolder(folder_path)
	checkFile(file_path, content)
}

// 检查 AND 写入为Data文件
// @param folder_path 保存的目录
// @param saving_path 文件保存位置
// @param online_url url地址
func checkAndWriteMedia(folder_path string, saving_path string, online_url string) {
	// check
	checkFolder(getSavingRootFolder())
	checkFolder(folder_path)
	checkMedia(saving_path, online_url)
}

// 检测/创建目标文件夹/目录
// @param folder_path 下载位置
func checkFolder(folder_path string) {
	// 检查路径, 如果不存在, 则创建
	path_exist, err := pathExists(folder_path)
	if err != nil {
		log.Fatal(err)
		return
	}

	if !path_exist {
		err := os.Mkdir(folder_path, os.ModePerm)
		if err != nil {
			log.Fatal(err)
			// 创建失败, 则关闭Golang Runtime!
			os.Exit(ERROR)
		}
	}
}

// 检测/创建目标文件
// @param file_path 完整目录位置
// @param content 写入内容
func checkFile(file_path string, content string) {
	// 是否要下载该文件
	wasWriteFile := true

	// 检查即将写入的下载文件, 如果存在, 则忽略; 否则下载并写入该空的文件中
	file_exists, err := pathExists(file_path)
	if err != nil {
		log.Fatal(err)
		wasWriteFile = false
	}

	if file_exists {
		wasWriteFile = false
	}

	if !wasWriteFile {
		return
	}

	fmt.Printf(WRITE_FILE_TIPS, file_path)
	writeFile([]byte(content), file_path)
}

// 检测/下载media文件
// @param saving_path 保存位置
// @param online_url url地址
func checkMedia(saving_path string, online_url string) {
	// 是否要下载该文件
	wasDownloadFile := true

	// 检查即将写入的下载文件, 如果存在, 则忽略; 否则下载并写入该空的文件中
	file_exists, err := pathExists(saving_path)
	if err != nil {
		log.Fatal(err)
		wasDownloadFile = false
	}

	if file_exists {
		fmt.Println(fmt.Sprintf(FILE_ALREADY_EXISTS_TIPS_TIPS, saving_path))
		wasDownloadFile = false
	}

	if !wasDownloadFile {
		return
	}

	// download_file(prepared to write byte[] data)
	out, err := os.Create(saving_path)
	if err != nil {
		log.Fatal(err)
	}
	defer out.Close()

	// 此处使用普通的Get下载
	resp, err := http.Get(online_url)
	if err != nil {
		log.Fatal(err)
	}

	defer resp.Body.Close()

	io.Copy(out, resp.Body)
}

// 获取保存的根目录(以`username`作为基准)
// @return 保存的根目录
func getSavingRootFolder() string {
	return dotStrWithOsSlashes() + cnf.dict.GetStr("USERNAME")
}

// 获取保存Media的根目录(以`username`作为基准)
// @return 保存Media的根目录
func getMediaFolder() string {
	return getSavingRootFolder() + getOsSlashes() + MEDIA_FOLDER_NAME
}

// returns a non-negative pseudo-random 31-bit integer as an int32
func getRandomNumber() string {
	return int2String(int(rand.Int31()))
}

// convert int 2 string
func int2String(i int) string {
	return strconv.Itoa(i)
}

// convert int32 2 string
func int322String(i int32) string {
	return strconv.FormatInt(int64(i), 10)
}

// convert int64 2 string
func int642String(i int64) string {
	return strconv.FormatInt(i, 10)
}

// convert int64 to int
func int642int(i int64) int {
	return int(i)
}

// 封装为简单的POST请求
// @param method_type MethodType
// @param request_url POST请求地址
// @param params 请求参数字典
// @param cookies 所有的cookies
// @return <body内容, []cookie, error>
func postSimpleReq(method_type MethodType, request_url string,
	params map[string]string, cookies []*http.Cookie) ([]byte, []*http.Cookie, error) {
	http_client := &http.Client{}
	request_params := url.Values{}

	if params != nil {
		for k, v := range params {
			request_params.Add(k, v)
		}
	}

	req, err := http.NewRequest(string(method_type), request_url, strings.NewReader(request_params.Encode()))
	for k, v := range DEFAULT_REQUEST_HEADERS {
		req.Header.Set(k, v)
	}

	if cookies != nil {
		for _, v := range cookies {
			req.AddCookie(v)
		}
	}

	resp, err := http_client.Do(req)
	defer resp.Body.Close()
	if err != nil {
		return nil, nil, err
	}

	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, nil, err
	}

	return body, resp.Cookies(), nil
}

// 写入内容到文件中
// @param result 写入的
// @param path 文件的完整路径
// @return 是否允许写入
func writeFile(result []byte, path string) bool {
	file, err := os.Create(path)
	if err != nil {
		log.Fatal(err)
		return false
	}

	defer file.Close()
	writer := bufio.NewWriterSize(file, len(result))
	err = ioutil.WriteFile(path, result, os.ModePerm)
	if err != nil {
		log.Fatal(err)
		return false
	}

	writer.Flush()
	return true
}

// 判定是否存在文件、文件夹
// @param path 被判定的: 文件/文件夹
// @return <是否存在, error>
func pathExists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}

	if os.IsNotExist(err) {
		return false, nil
	}

	return false, err
}

// (实际大小)读取完整的文件
// @param path 文件的路径
// @return 读取到的内容
func readFile(path string) []byte {
	file, err := os.Open(path)
	if err != nil {
		log.Fatal(err)
	}

	defer file.Close()
	reader := bufio.NewReader(file)
	var result []byte
	result, err = ioutil.ReadAll(reader)
	if err != nil {
		log.Fatal(err)
	}

	return result
}

// get caller-funcName
// @return function-name
func funcName() string {
	pc, _, _, _ := runtime.Caller(1)
	return runtime.FuncForPC(pc).Name()
}

// 只针对windows操作系统特殊处理
// @return osSlashes
func getOsSlashes() string {
	if runtime.GOOS == "windows" {
		return WINDOWS_OS_SLASHES
	}

	return NORMAL_SLASHES
}

// DOT_STR_WITH_OS_SLASHES
// @return DOT_STR_WITH_OS_SLASHES
func dotStrWithOsSlashes() string {
	return DOT_STR + getOsSlashes()
}

// run with recover!
// @param parser TQQParser
// @param retry_count current: retry_count
func runWithRecover(parser TQQParser, retry_count *int32) {
	defer func() {
		if e := recover(); e != nil {
			new_retry_count := atomic.AddInt32(retry_count, 1)
			if new_retry_count >= DEFAULT_MAX_RETRY_COUNT {
				panic(RETRY_TOO_MANY_TIPS)
			} else if new_retry_count > 0 {
				fmt.Printf(RETRY_FETCH_TIPS, new_retry_count)
				time.Sleep(DEFAULT_RETRY_SLEEP_SECONDS)
				runWithRecover(parser, retry_count)
			}
		}
	}()

	for {
		parser.GetData()
		parser.WriteData(DEFAULT_DATA_TYPE)
		atomic.AddInt32(retry_count, -atomic.LoadInt32(retry_count))
	}
}

// read-write object
type RWDict struct {
	// 针对map的读写锁
	rwLock sync.RWMutex
	// mapping-data
	mapping map[string]interface{}
}

// get
// @param k key
// @return value
func (rw *RWDict) Get(k string) interface{} {
	rw.rwLock.RLock()
	defer rw.rwLock.RUnlock()
	v, _ := rw.mapping[k]
	return v
}

// get-value(string)
// @param k key
// @return value(string-type)
func (rw *RWDict) GetStr(k string) string {
	v := rw.Get(k)
	if v == nil {
		return EMPTY_STR
	}

	return v.(string)
}

// put
// @param k key
// @param v value
func (rw *RWDict) Put(k string, v interface{}) {
	rw.rwLock.Lock()
	defer rw.rwLock.Unlock()
	rw.mapping[k] = v
}

// remove
// @param k key
func (rw *RWDict) Remove(k string) {
	rw.rwLock.Lock()
	defer rw.rwLock.Unlock()
	delete(rw.mapping, k)
}

// 定义配置文件结构体, 组合自RWDict
type Config struct {
	// dict(config-core)
	dict RWDict
}

// init-config
func (conf *Config) init() {
	if conf.dict.mapping == nil {
		conf.dict.mapping = make(map[string]interface{})
	}

	result := readFile(DEFAULT_SETTINGS_CNF_PATH)
	if result == nil {
		log.Fatal(CNF_FILE_EXISTS_TIPS)
		return
	}

	eval_result := string(result)
	cnf_vals := strings.Split(eval_result, string(NEXT_LINE_CHAR))
	if cnf_vals == nil {
		log.Fatal(CNF_FILE_WAS_RIGHT_TIPS)
		return
	}

	for _, v := range cnf_vals {
		if v == EMPTY_STR {
			continue
		} else if strings.Index(v, EQUAL_SIGN) == -1 {
			log.Fatalf(CNF_FORMAT_ERROR_TIPS, v)
			return
		} else if strings.Index(v, HASH_SIGN) == 0 {
			continue
		}

		key := v[:strings.Index(v, EQUAL_SIGN)]
		value := v[strings.Index(v, EQUAL_SIGN)+1:]
		conf.dict.Put(key, value)
	}
}

// initial-method
func init() {
	once.Do(func() {
		cnf = &Config{}
		cnf.init()

		// setting-cookies
		if _, ok := DEFAULT_REQUEST_HEADERS["Cookie"]; ok {
		} else {
			DEFAULT_REQUEST_HEADERS["Cookie"] = cnf.dict.GetStr("DEFAULT_COOKIES")
		}

		// setting reference-url
		if _, ok := DEFAULT_REQUEST_HEADERS["rf"]; ok {
		} else {
			DEFAULT_REQUEST_HEADERS["rf"] = fmt.Sprintf(REFERENCE_PAGE_URL_TEMPLATE, cnf.dict.GetStr("USERNAME"))
		}

		data_type := cnf.dict.GetStr("EXPORT_DATA_TYPE")
		if data_type != EMPTY_STR {
			DEFAULT_DATA_TYPE = DataType(data_type)
		}
	})
}

// main-method
func main() {
	parser := TQQParser{}
	parser.Initial()

	retry_count := new(int32)
	runWithRecover(parser, retry_count)
}
