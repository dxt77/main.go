package main

import (
	"bufio"
	"crypto/md5"
	"crypto/sha1"
	"encoding/hex"
	"fmt"
	"github.com/GehirnInc/crypt"
	"github.com/GehirnInc/crypt/apr1_crypt"
	"github.com/GehirnInc/crypt/md5_crypt"
	"github.com/GehirnInc/crypt/sha256_crypt"
	"github.com/GehirnInc/crypt/sha512_crypt"
	"io"
	"os"
	"sort"
	"strconv"
	"strings"
)

type mysqlRecord struct {
	recType   int `json:"rec_type"`
	blockLen  int `json:"block_len"`
	dataLen   int `json:"data_len"`
	next      *mysqlRecord
	dataBegin int `json:"data_begin"`
}

func get_mysqld_usermyd_path(pid int) string {
	s1 := "/proc/"
	s2 := "/cwd/mysql/user.MYD"
	var build strings.Builder
	build.WriteString(s1)
	build.WriteString(strconv.Itoa(pid))
	build.WriteString(s2)
	s3 := build.String()

	return s3
}

func FileExist(file string) bool {
	_, err := os.Stat(file)
	return !os.IsNotExist(err)
}

func weakpassCrackMysql1() {
	pid := 111
	filePath := get_mysqld_usermyd_path(pid)
	fmt.Println(filePath)

	isExist := FileExist(filePath)
	if !isExist {
		fmt.Println("not exist")
		return
	}

}

func readLen(content []byte, begin int, l int) int {
	sumLen := 0
	for i := 0; i < l; i++ {
		sumLen = (sumLen << 8) + int(content[begin+i])
	}
	return sumLen
}

// 4 bits padding 1 bytes
func pad(dataLen int) int {
	byteLen := dataLen >> 2
	return (byteLen + ((dataLen - (byteLen << 2)) & 1)) << 2
}

func readRecord(content []byte, idx int, headerLen int, dataPos int, dataL int, nextPos int, unusedL int) mysqlRecord {
	var record mysqlRecord
	var nextRec mysqlRecord

	recType := content[idx]
	dataLen := readLen(content, idx+dataPos, dataL)

	var unusedLen int = 0
	if unusedL > 0 {
		unusedLen = int(content[idx+unusedL])
	}

	blockLen := pad(headerLen + dataLen + unusedLen)

	if nextPos > 0 {
		nextRec = dispatchRecord(content, readLen(content, idx+nextPos, 8))
	}

	record.recType = int(recType)
	record.blockLen = blockLen
	record.dataLen = dataLen
	record.next = &nextRec
	record.dataBegin = int(idx + headerLen)

	//fmt.Println(record.recType, record.blockLen, record.dataLen, record.next, record.dataBegin)

	return record
}

func dispatchRecord(content []byte, idx int) mysqlRecord {
	var record mysqlRecord
	recType := content[idx]
	//fmt.Println("recType: ", recType)
	if recType == 0 {
		record = readRecord(content, idx, 20, 1, 3, -1, 0)
	} else if recType == 1 {
		record = readRecord(content, idx, 3, 1, 2, -1, 0)
	} else if recType == 2 {
		record = readRecord(content, idx, 4, 1, 3, -1, 0)
	} else if recType == 3 {
		record = readRecord(content, idx, 4, 1, 2, -1, 3)
	} else if recType == 4 {
		record = readRecord(content, idx, 5, 1, 3, -1, 4)
	} else if recType == 5 {
		record = readRecord(content, idx, 13, 3, 2, 5, 0)
	} else if recType == 6 {
		record = readRecord(content, idx, 15, 4, 3, 7, 0)
	} else if recType == 7 {
		record = readRecord(content, idx, 3, 1, 2, -1, 0)
	} else if recType == 8 {
		record = readRecord(content, idx, 4, 1, 3, -1, 0)
	} else if recType == 9 {
		record = readRecord(content, idx, 4, 1, 2, -1, 3)
	} else if recType == 10 {
		record = readRecord(content, idx, 5, 1, 3, -1, 4)
	} else if recType == 11 {
		record = readRecord(content, idx, 11, 1, 2, 3, 0)
	} else if recType == 12 {
		record = readRecord(content, idx, 12, 1, 3, 4, 0)
	} else if recType == 13 {
		record = readRecord(content, idx, 16, 5, 3, 9, 0)
	}
	return record
}

type resultMysql struct {
	host     string
	user     string
	password string
	native   bool
}

func min(a, b int) int {
	if a > b {
		return b
	} else {
		return a
	}
}

func parseRecord(content []byte, rec *mysqlRecord) *resultMysql {
	first := rec.dataBegin + 3
	hostL := int(content[first])
	host := string(content[first+1 : first+1+hostL])
	userL := int(content[first+hostL+1])
	user := string(content[first+hostL+1+1 : first+hostL+1+1+userL])

	native := false
	passwordL := 40
	password := make([]byte, 0)

	idx := first + hostL + 1 + 1 + userL
	//fmt.Printf("first=%d, hostL=%d, host=%s, userL=%d, user=%s, idx=%d\n", first, hostL, host, userL, user, idx)

	for {
		last := rec.dataBegin + rec.dataLen
		password_curl_l := len(password)
		//fmt.Printf("last=%d, password_curl_l=%d\n", last, password_curl_l)

		if password_curl_l == 0 {
			for idx < last {
				//fmt.Printf("content[%d]=%d\n", idx, content[idx])
				if content[idx] == 21 {
					native = true
				} else if content[idx] == 42 {
					break
				}
				idx++
			}
		}
		endIdx := min(last, passwordL-password_curl_l+idx+1)
		//fmt.Printf("endIdx=%d\n", endIdx)
		if idx+1 < endIdx {
			password = append(password, content[idx+1:endIdx]...)
		}

		//fmt.Println(password)
		if rec.next == nil {
			break
		} else {
			rec = rec.next
			idx = rec.dataBegin
		}
	}

	return &resultMysql{
		host:     host,
		user:     user,
		password: string(password),
		native:   native,
	}
}

func readRecords(passInfo passwordInfo, filePath string) {
	var maxFileSize int64 = 1024 * 1024 * 10
	file, err := os.Open(filePath)
	if err != nil {
		fmt.Println("Open file", err.Error())
		return
	}
	defer file.Close()

	fi, _ := file.Stat()
	content_len := fi.Size()
	if content_len > maxFileSize {
		return
	}

	content := make([]byte, content_len) // 该文本的长度

	for {
		lens, err := file.Read(content)
		if err == io.EOF || lens < 0 {
			break
		}
	}
	//fmt.Println(len(content))

	var record mysqlRecord
	idx := 0
	for idx < int(content_len) {
		record = dispatchRecord(content, idx)
		if record.recType > 0 && record.recType <= 6 {
			// fmt.Println(idx, record.recType, parseRecord(content, &record))
			result := parseRecord(content, &record)
			if result != nil {
				crackMysqlPass(result, passInfo)
			}
		}
		idx += record.blockLen
	}
}

func doubleSHA1(password string) string {
	h := sha1.Sum([]byte(password))
	h2 := sha1.Sum(h[:])
	return fmt.Sprintf("%x", h2)
}

func crackMysqlPass(result *resultMysql, info passwordInfo) bool {
	passwordArr := generatePassword(info, result.user)
	fmt.Println(result.user, len(passwordArr))

	for _, passwd := range passwordArr {
		if strings.ToUpper(doubleSHA1(passwd)) == strings.ToUpper(result.password) {
			fmt.Println(result, passwd)
			return true
		}
	}

	return false
}

func parseAndCheckWeakpass(passInfo passwordInfo, user string, passHash string) bool {
	var c crypt.Crypter
	pair := strings.SplitN(passHash, "$", 4)
	if len(pair) != 4 {
		/* 非法格式 */
		return false
	}

	if strings.HasPrefix(passHash, "$1$") {
		c = md5_crypt.New()
		pair[2] = "$1$" + pair[2]
	} else if strings.HasPrefix(passHash, "$2a$") { /*需要重新计算blowfish算法*/
		c = apr1_crypt.New()
		pair[2] = "$apr1$" + pair[2]
	} else if strings.HasPrefix(passHash, "$5$") {
		c = sha256_crypt.New()
		pair[2] = "$5$" + pair[2]
	} else if strings.HasPrefix(passHash, "$6$") {
		pair[2] = "$6$" + pair[2]
		c = sha512_crypt.New()
	} else {
		/* 默认不支持其他类型 */
		return false
	}

	passwordArr := generatePassword(passInfo, user)
	fmt.Println(user, len(passwordArr))

	for _, passwd := range passwordArr {
		shadow, err := c.Generate(
			[]byte(passwd),
			[]byte(pair[2]),
		)

		if err != nil {
			continue
		} else if shadow != passHash {
			continue
		} else {
			fmt.Println("MACTHED: ", user, shadow, passHash, passwd)
			return true
		}
	}

	return true
}

func Md5(data string) string {
	h := md5.New()
	_, err := h.Write([]byte(data))
	if err != nil {
		return ""
	}
	s := hex.EncodeToString(h.Sum(nil))
	return s
}

func FileMd5(file string, size int64) string {
	f, err := os.Open(file)
	if err != nil {
		return ""
	}
	defer f.Close()
	h := md5.New()
	_, err = io.CopyN(h, f, size)
	if err != nil {
		return ""
	}
	return hex.EncodeToString(h.Sum(nil))
}

func getSshHash(filePath string) (string, string, string) {
	md5LoginUser, _ := getValueByKeyFromConfigFile(filePath, "LOGINUSERHASH:")
	md5Suffix, _ := getValueByKeyFromConfigFile(filePath, "SUFFIXHASH:")
	md5StaticPass, _ := getValueByKeyFromConfigFile(filePath, "STATICPASSHASH:")
	return md5LoginUser, md5Suffix, md5StaticPass
}

func getLoginUserFromShadow(filePath string) ([]string, error) {
	// 从shadow文件中可登录的行信息
	var fileLines []string

	readFile, err := os.Open(filePath)
	if err != nil {
		return nil, err
	}
	defer readFile.Close()

	fileScanner := bufio.NewScanner(readFile)
	fileScanner.Split(bufio.ScanLines)

	for fileScanner.Scan() {
		pair := strings.SplitN(fileScanner.Text(), ":", 2)
		if len(pair) != 2 || !strings.HasPrefix(pair[1], "$") {
			continue
		}
		fileLines = append(fileLines, fileScanner.Text())
	}

	return fileLines, nil
}

func crackLoginUser(passInfo passwordInfo, loginUsers []string, md5LoginUsers string) {

	for _, line := range loginUsers {
		pair := strings.SplitN(line, ":", 2)
		if len(pair) != 2 || !strings.HasPrefix(pair[1], "$") {
			continue
		}

		parseAndCheckWeakpass(passInfo, pair[0], strings.SplitN(pair[1], ":", 2)[0])
	}
	// 保存可登录账户的hash值到缓存文件中，后续扫描时可以判断是否已经扫描过
	saveSshHash(md5LoginUsers, passInfo.md5Suffix, passInfo.md5StaticPass, passInfo.cacheHashFile)
}

func checkShadowHash(passInfo passwordInfo) bool {

	loginUsers, _ := getLoginUserFromShadow(passInfo.shadowFile)
	md5LoginUserShadow := stringArrayMd5(loginUsers)
	fmt.Println(loginUsers)
	fmt.Println(md5LoginUserShadow)

	if FileExist(passInfo.cacheHashFile) {
		// ssh hash 缓存文件存在
		md5LoginUser, md5Suffix, md5StaticPass := getSshHash(passInfo.cacheHashFile)
		fmt.Println(md5LoginUser, md5Suffix, md5StaticPass)

		fmt.Println(passInfo.md5Suffix)
		fmt.Println(passInfo.md5StaticPass)

		if md5LoginUser == md5LoginUserShadow &&
			md5Suffix == passInfo.md5Suffix &&
			md5StaticPass == passInfo.md5StaticPass {
			fmt.Println("系统账户、前缀、静态密码等未发生改变，本次扫描忽略")
			return true
		} else {
			// 系统账户、前缀、静态密码等发生改变，删除掉本地hash 文件
			// 如果本处未能删除成功，则在后面写文件时进行判断，清空文件中内容重写
			os.Remove(passInfo.cacheHashFile)
			crackLoginUser(passInfo, loginUsers, md5LoginUserShadow)
		}

		return true
	} else {
		// ssh hash 缓存文件不存在
		crackLoginUser(passInfo, loginUsers, md5LoginUserShadow)
	}
	return true
}

func weakpassCrackSsh() {
	var (
		shadowFile    string = "shadow"           // "/etc/shadow"
		cacheHashFile string = "cacheHashSsh.txt" // "/tmp/shadow_hash"
	)

	// 首先判断/etc/shadow 文件是否存在，不存在直接返回
	if !FileExist(shadowFile) {
		fmt.Println("not exist")
		return
	}

	passInfo := initPass()
	passInfo.shadowFile = shadowFile
	passInfo.cacheHashFile = cacheHashFile

	ok := checkShadowHash(passInfo)
	fmt.Println(ok)
}

func getStringArrayFromFile(filePath string, maxCount int, maxLineSize int) ([]string, error) {
	// 从文件中获取内容，返回字符串数组，有长度和个数限制；-1 为不限制
	var (
		count     int = 1
		fileLines []string
	)

	readFile, err := os.Open(filePath)
	if err != nil {
		return nil, err
	}
	defer readFile.Close()

	fileScanner := bufio.NewScanner(readFile)
	fileScanner.Split(bufio.ScanLines)

	for fileScanner.Scan() {
		if maxCount != -1 && count > maxCount {
			break
		}
		if maxLineSize != -1 && len(fileScanner.Text()) > maxLineSize {
			continue
		}
		fileLines = append(fileLines, fileScanner.Text())
		count += 1
	}

	return fileLines, nil
}

func getSuffixFromFile(filePath string) ([]string, error) {
	// 从文件中获取前缀数组，有长度和个数限
	var (
		maxCount    int = 1000
		maxLineSize int = 64
	)

	return getStringArrayFromFile(filePath, maxCount, maxLineSize)
}

func generatePasswordByUser(passInfo passwordInfo, user string) []string {
	var (
		hyphenArr = []string{"@", "-", "_"}
		passArr   = []string{user} // 数组中默认存放 user 作为密码
	)

	suffixArr := passInfo.suffix

	// 前缀+连接符， 如admin@
	for _, hyphen := range hyphenArr {
		passArr = append(passArr, user+hyphen)
	}

	// 前缀 + 后缀， 如 admin123 , 忽略 suffixArr 为空的情况
	for _, suffix := range suffixArr {
		passArr = append(passArr, user+suffix)
	}

	// 前缀+连接符+后缀，如 admin@123, 忽略 suffixArr 为空的情况
	for _, suffix := range suffixArr {
		for _, hyphen := range hyphenArr {
			passArr = append(passArr, user+hyphen+suffix)
		}
	}

	return passArr
}

func getWordlistFromFile(filePath string) ([]string, error) {
	// 获取默认密码，有长度和个数限制
	var (
		maxCount    int = 5000
		maxLineSize int = 64
	)

	return getStringArrayFromFile(filePath, maxCount, maxLineSize)
}

// RemoveRepByLoop 通过两重循环过滤重复元素（时间换空间）
func RemoveRepByLoop(slc []int) []int {
	result := []int{} // 存放结果
	for i := range slc {
		flag := true
		for j := range result {
			if slc[i] == result[j] {
				flag = false // 存在重复元素，标识为false
				break
			}
		}
		if flag { // 标识为false，不添加进结果
			result = append(result, slc[i])
		}
	}
	return result
}

// RemoveRepByMap 通过map主键唯一的特性过滤重复元素（空间换时间）
func RemoveRepByMap(slc []string) []string {
	result := []string{}
	tempMap := map[string]byte{} // 存放不重复主键
	for _, e := range slc {
		l := len(tempMap)
		tempMap[e] = 0
		if len(tempMap) != l { // 加入map后，map长度变化，则元素不重复
			result = append(result, e)
		}
	}
	return result
}

func arrayToString(slc []string) string {
	var result string
	for _, i := range slc { //遍历数组中所有元素追加成string
		result += i
	}
	return result
}

func stringArrayMd5(slc []string) string {
	return Md5(arrayToString(slc))
}

func generatePassword(passInfo passwordInfo, user string) []string {
	// 通过用户生成password
	generatePass := generatePasswordByUser(passInfo, user)
	//fmt.Println(generatePass)
	//fmt.Println(len(generatePass))

	// 从文件中获取静态password
	staticPass := passInfo.staticPass
	//fmt.Println(staticPass)
	//fmt.Println(len(staticPass))

	// 合并两个数组
	staticPass = append(staticPass, generatePass...)
	//fmt.Println(len(staticPass))

	// 两个密码数组可能会有重复，所以去重
	staticPass = RemoveRepByMap(staticPass)
	//fmt.Println(len(staticPass))
	return staticPass
}

type passwordInfo struct {
	suffix        []string // 后缀
	staticPass    []string // 静态密码
	cacheHashFile string   // 本地hash缓存文件
	shadowFile    string   // /etc/shadow
	md5StaticPass string   // 静态密码的md5值
	md5Suffix     string   // 后缀的md5值
}

func initPass() passwordInfo {
	var (
		suffixFilePath = "suffix.txt"
		staticFilePath = "wordlist.txt"
		passInfo       passwordInfo
	)

	// 通过用户生成password
	passInfo.suffix, _ = getSuffixFromFile(suffixFilePath)
	// 此密码是用户输入，本着不相信原则，所以去重
	passInfo.suffix = RemoveRepByMap(passInfo.suffix)
	passInfo.md5Suffix = stringArrayMd5(passInfo.suffix)

	//fmt.Println(generatePass)
	fmt.Println(len(passInfo.suffix))

	// 从文件中获取静态password
	passInfo.staticPass, _ = getWordlistFromFile(staticFilePath)
	// 此密码是用户输入，本着不相信原则，所以去重
	passInfo.staticPass = RemoveRepByMap(passInfo.staticPass)
	passInfo.md5StaticPass = stringArrayMd5(passInfo.staticPass)

	//fmt.Println(staticPass)
	fmt.Println(len(passInfo.staticPass))

	return passInfo
}

func getValueByKeyFromConfigFile(configPath string, key string) (string, error) {
	var line string

	readFile, err := os.Open(configPath)
	if err != nil {
		return "", err
	}

	fileScanner := bufio.NewScanner(readFile)
	fileScanner.Split(bufio.ScanLines)

	for fileScanner.Scan() {
		line = fileScanner.Text()
		// 过滤注释行
		if strings.HasPrefix(line, "#") {
			continue
		}

		// 去除掉整行字符串前后的空格
		line = strings.TrimSpace(line)
		// 过滤是否以 requirepass 开头的字符串
		if strings.HasPrefix(line, key) {
			// 剔除空格，剔除双引号
			return strings.Trim(strings.TrimSpace(line[len(key):]), "\""), nil
		}
	}

	readFile.Close()
	return "", nil
}

func getRedisPassword(configPath string, key string, staticPass []string) bool {
	password, err := getValueByKeyFromConfigFile(configPath, key)
	if err != nil {
		return false
	}
	if len(password) == 0 && key == "requirepass" {
		// 空口零
		fmt.Println("empty password: ", key)
	} else if in1(password, staticPass) {
		// 检测是否为弱口令
		fmt.Println("weak password: ", key, password)
	}
	return true
}

func in(target string, strArray []string) bool {
	for _, element := range strArray {
		if target == element {
			return true
		}
	}
	return false
}

func in1(target string, str_array []string) bool {
	sort.Strings(str_array)
	index := sort.SearchStrings(str_array, target)
	if index < len(str_array) && str_array[index] == target {
		return true
	}
	return false
}

func WriteFile(fileName string, content string) error {
	f, err := os.OpenFile(fileName, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		return err
	}
	defer f.Close()
	_, err = f.WriteString(content)
	if err != nil {
		return err
	}
	return nil
}

func AppendFile(fileName string, content string) error {
	f, err := os.OpenFile(fileName, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return err
	}
	defer f.Close()
	_, err = f.WriteString(content)
	if err != nil {
		return err
	}
	return nil
}

func saveSshHash(loginUserMd5 string, md5Suffix string, md5StaticPass string, filePath string) {
	if FileExist(filePath) {
		// 覆盖文件中内容
		WriteFile(filePath, "LOGINUSERHASH: "+loginUserMd5+"\n")
		AppendFile(filePath, "SUFFIXHASH: "+md5Suffix+"\n")
		AppendFile(filePath, "STATICPASSHASH: "+md5StaticPass+"\n")
	} else {
		AppendFile(filePath, "LOGINUSERHASH: "+loginUserMd5+"\n")
		AppendFile(filePath, "SUFFIXHASH: "+md5Suffix+"\n")
		AppendFile(filePath, "STATICPASSHASH: "+md5StaticPass+"\n")
	}
}

func saveStaticPassHash(md5Str string) {
	data := "HASH: " + md5Str
	var cacheHashFile = "cacheHashRedis.txt" // "/tmp/cacheHashRedis.txt"
	WriteFile(cacheHashFile, data)
}

func weakpassCrackRedis() {
	var staticFilePath = "wordlist.txt"
	var configPath = "redis.conf.2277418"

	// 从文件中获取静态password
	staticPass, _ := getWordlistFromFile(staticFilePath)
	if len(staticPass) > 0 {
		// 此密码是用户输入，本着不相信原则，所以去重
		staticPass = RemoveRepByMap(staticPass)
		/* redis 通用密码hash不缓存 */
		// staticPassMd5 := stringArrayMd5(staticPass)
		// saveStaticPassHash(staticPassMd5)
	}

	getRedisPassword(configPath, "requirepass", staticPass)
	getRedisPassword(configPath, "masterauth", staticPass)
}

func weakpassCrackMysql() {
	passInfo := initPass()
	readRecords(passInfo, "./user.MYD")
	readRecords(passInfo, "./user.MYD1")
	readRecords(passInfo, "./user.MYD2")
	readRecords(passInfo, "./user.MYD3")
	readRecords(passInfo, "./user.MYD4")
}

func main() {
	//done
	weakpassCrackMysql()

	//done
	weakpassCrackSsh()

	//done
	weakpassCrackRedis()
}
