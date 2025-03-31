// walog by suirosu exgaya epowsal wlb iwlb@outlook.com exgaya@gmail.com 20241230;

package imap

import (
	"bufio"
	"bytes"
	"compress/flate"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"math/rand"
	"os"
	"reflect"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"time"
	"unsafe"
)

var logf *os.File

func InitLog() {
	log.SetFlags(log.Lshortfile | log.Ldate | log.Ltime | log.LstdFlags)
	var loge error
	logf, loge = os.OpenFile(os.Args[0]+".log", os.O_CREATE|os.O_WRONLY, 0666)
	if loge == nil {
		logf.Seek(0, os.SEEK_END)
		log.SetOutput(logf)
	} else {
		P("log file", os.Args[0]+".log", "open log error", loge)
	}
}

func ChangeLogPath(path string) error {
	var loge error
	if strings.LastIndexAny(path, "/\\") != -1 {
		os.MkdirAll(path[:strings.LastIndexAny(path, "/\\")], 0666)
	}
	if logf != nil {
		logf.Close()
	}
	log.SetFlags(log.Lshortfile | log.Ldate | log.Ltime | log.LstdFlags)
	logf, loge = os.OpenFile(path, os.O_CREATE|os.O_WRONLY, 0666)
	if loge == nil {
		logf.Seek(0, os.SEEK_END)
		log.SetOutput(logf)
	} else {
		P("log file", path, "open error", loge)
	}
	return nil
}

var LogStackDeep int = 8
var LogStackLineEnd string = "<<" //\n or <<;
var LogWrapSize int = 512

func E(as ...any) error {
	panic(string(append(sp(as...), skz()...)))
}

func e(as ...any) error {
	return errors.New(string(append(sp(as...), skz()...)))
}

func L(as ...any) {
	if logf == nil {
		InitLog()
	}
	log.Println(string(append(sp(as...), skz()...)))
}

func l(as ...any) {
	if logf == nil {
		InitLog()
	}
	log.Println(string(sp(as...)))
}

func P(as ...any) {
	fmt.Println(string(append(sp(as...), skz()...)), time.Now().Format(time.RFC3339Nano))
}

func p(as ...any) {
	fmt.Println(string(sp(as...)))
}

func LP(as ...any) {
	if logf != nil {
		log.Println(string(append(sp(as...), skz()...)))
	}
	fmt.Println(string(append(sp(as...), skz()...)), time.Now().Format(time.RFC3339Nano))
}

func Lp(as ...any) {
	if logf != nil {
		log.Println(string(append(sp(as...), skz()...)))
	}
	fmt.Println(string(sp(as...)), time.Now().Format(time.RFC3339Nano))
}

func lp(as ...any) {
	if logf != nil {
		log.Println(string(sp(as...)))
	}
	fmt.Println(string(sp(as...)))
}

func c(as ...any) {
	if len(as) == 2 {
		srl := sp(as[0])
		if len(srl) > 0 {
			srl = srl[:len(srl)-1]
		}
		srl1 := sp(as[1])
		if len(srl1) > 0 {
			srl1 = srl1[:len(srl1)-1]
		}
		if string(srl) != string(srl1) {
			E(string(srl), "!=", string(srl1))
		} else {
			return
		}
	} else if len(as) > 1 && reflect.TypeOf(as[0]).String() == "string" {
		srl := sp(as[1:]...)
		if len(srl) > 0 {
			srl = srl[:len(srl)-1]
		}
		if as[0].(string) != string(srl) {
			E(append([]any{as[0].(string)}, as[1:]...)...)
		}
	} else if len(as) == 1 && reflect.TypeOf(as[0]).String() == "bool" {
		if !as[0].(bool) {
			E("expression false error")
		}
	} else {
		E("Ck using error")
	}
}

// list to any list
func ta(a ...any) []any {
	return a
}

// current stack;
func skz() []byte {
	var stackbs []byte
	tbn := 0
	for i := 0; i <= LogStackDeep; i++ {
		pc, file, line, ok := runtime.Caller(i)
		if ok {
			sn := file[strings.LastIndex(file[:strings.LastIndex(file, "/")], "/")+1:]
			if !(strings.HasSuffix(sn, "/testing.go") || strings.HasSuffix(sn, "/walog.go")) && strings.HasSuffix(sn, ".s") == false {
				fc := runtime.FuncForPC(pc)
				stackbs = append(stackbs, []byte(fmt.Sprintf(logStrRepeat('\t', tbn)+"[%d %s]%s"+LogStackLineEnd, line, fc.Name(), sn))...)
				tbn += 1
			}
		}
	}
	return stackbs
}

func sks() string {
	return string(skz())
}

func sp(as ...any) []byte {
	var spr []byte
	prel := 0
	for _, a := range as {
		switch a.(type) {
		case string:
			spr = append(spr, []byte(fmt.Sprintf("%s^", a.(string)))...)
		case int:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(int)))...)
		case uint:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(uint)))...)
		case int8:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(int8)))...)
		case uint8:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(uint8)))...)
		case int16:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(int16)))...)
		case uint16:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(uint16)))...)
		case int32:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(int32)))...)
		case uint32:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(uint32)))...)
		case int64:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(int64)))...)
		case uint64:
			spr = append(spr, []byte(fmt.Sprintf("%d^", a.(uint64)))...)
		case float32:
			spr = append(spr, []byte(f4s(a.(float32))+"^")...)
		case float64:
			spr = append(spr, []byte(Fs(a.(float64))+"^")...)
		case error:
			spr = append(spr, []byte("error{"+a.(error).Error()+"}^")...)
		case bool:
			spr = append(spr, []byte(fmt.Sprintf("%t^", a.(bool)))...)
		case time.Time:
			spr = append(spr, []byte(fmt.Sprintf("%s^", a.(time.Time).Format(time.RFC3339)))...)
		default:
			spr = append(spr, []byte(fmt.Sprintf("%#v^", a))...)
		}
		if len(spr)-prel >= LogWrapSize {
			spr = append(spr, []byte("\n\t")...)
		}
		prel = len(spr)
	}
	if len(spr) > 0 {
		if spr[len(spr)-1] == '^' {
			spr[len(spr)-1] = '\t'
		} else if len(spr) >= 2 {
			spr = spr[:len(spr)-1]
			spr[len(spr)-1] = '\t'
		}
	}
	return spr
}

func logStrRepeat(b byte, n int) string {
	if LogStackLineEnd == "<<" {
		return ""
	}
	bs := []byte{}
	for i := 0; i < n; i += 1 {
		bs = append(bs, b)
	}
	return string(bs)
}

//wbase.go

type z = []byte
type s = string
type d = int64
type d4 = int32
type d2 = int16
type dd = int8
type u = uint64
type u4 = uint32
type u2 = uint16
type uu = uint8
type f = float64
type f4 = float32
type I = int
type U = uint
type sg = string
type ss = []string

var d0 = int64(0)
var d40 = int32(0)
var d20 = int16(0)
var do0 = int8(0)
var u0 = uint64(0)
var u40 = uint32(0)
var u20 = uint16(0)
var uo0 = uint8(0)
var f0 = float64(0)
var f40 = float32(0)
var I0 = int(0)
var U0 = uint(0)

var d1 = int64(1)
var d41 = int32(1)
var d21 = int16(1)
var do1 = int8(1)
var u1 = uint64(1)
var u41 = uint32(1)
var u21 = uint16(1)
var uo1 = uint8(1)
var f1 = float64(1)
var f41 = float32(1)
var I1 = int(1)
var U1 = uint(1)

const (
	KB = 1024
	MB = 1024 * 1024
	GB = 1024 * 1024 * 1024
	TB = 1024 * 1024 * 1024 * 1024
	PB = 1024 * 1024 * 1024 * 1024 * 1024
	EB = 1024 * 1024 * 1024 * 1024 * 1024 * 1024
)

const (
	PS = "/\\"
)

// path seporate symbol;
func ps() string {
	if runtime.GOOS == "windows" {
		return "\\"
	} else {
		return "/"
	}
}

// is path dir;
func ipd(pa s) bool {
	if len(pa) > 0 && (pa[len(pa)-1] == '/' || pa[len(pa)-1] == '\\') {
		return true
	}
	return false
}

func pstd(path string) string {
	return regexp.MustCompile("[/\\\\]+").ReplaceAllString(path, ps())
}

// uint64 to string;
func uh(v u) string {
	return fmt.Sprintf("%016X", v)
}

// uint64 to string;
func us(v u) string {
	return strconv.FormatUint(v, 10)
}

// string to uint64;
func su(v string) (uv u) {
	uv, _ = strconv.ParseUint(v, 10, 64)
	return uv
}

// int64 to sting;
func ds(v d) string {
	return strconv.FormatInt(v, 10)
}

// string to int64;
func sd(v string) (uv d) {
	uv, _ = strconv.ParseInt(v, 10, 64)
	return uv
}

// float64 to string;
func Fs(v f) string {
	return fr(v, 15)
}

// string to float64;
func sf(v string) (fv f) {
	fv, _ = strconv.ParseFloat(v, 64)
	return fv
}

// float32 to string;
func f4s(v float32) string {
	return strconv.FormatFloat(float64(v), 'g', 6, 32)
}

// string to float32;
func sf4(v string) (f4v f4) {
	fv, _ := strconv.ParseFloat(v, 32)
	return f4(fv)
}

// int to string;
func Is(v I) string {
	return strconv.FormatInt(int64(v), 10)
}

// string to int;
func sI(v string) (uv I) {
	uv2, _ := strconv.ParseInt(v, 10, 64)
	return I(uv2)
}

// uint to string
func Us(v U) string {
	return strconv.FormatUint(u(v), 10)
}

// string to uint
func sU(v string) (uv U) {
	uv2, _ := strconv.ParseUint(v, 10, 64)
	return U(uv2)
}

// fliat64 round;
func fr(v float64, roundn int) string {
	if roundn > 15 {
		roundn = 15
	}
	return fmt.Sprintf("%."+strconv.Itoa(roundn)+"f", v)
}

func fcmp(v1, v2 float64) int {
	dv := v1 - v2
	if math.Abs(dv) < math.Abs((v1+v2)/1e15) {
		return 0
	} else if dv < 0 {
		return -1
	} else {
		return 1
	}
}

func fcmpn(v1, v2 float64, dotn int) int {
	dv := v1 - v2
	if math.Abs(dv) < math.Abs((v1+v2)/math.Pow(10, f(dotn))) {
		return 0
	} else if dv < 0 {
		return -1
	} else {
		return 1
	}
}
func af(a any) float64 {
	switch a.(type) {
	case int8:
		return f(a.(int8))
	case int16:
		return f(a.(int16))
	case int32:
		return f(a.(int32))
	case int64:
		return f(a.(int64))
	case uint8:
		return f(a.(uint8))
	case uint16:
		return f(a.(uint16))
	case uint32:
		return f(a.(uint32))
	case uint64:
		return f(a.(uint64))
	case int:
		return f(a.(int))
	case uint:
		return f(a.(uint))
	case float32:
		return f(a.(float32))
	case float64:
		return f(a.(float64))
	case string:
		return sf(a.(string))
	case []byte:
		return sf(s(a.([]byte)))
	default:
		P("type error")
	}
	return 0
}

func NB(siz any) string {
	var size = af(siz)
	if size < 1024 {
		return us(u(size)) + "byte"
	} else if size < 1024*1024 {
		return fr(float64(size)/1024, 2) + "KB"
	} else if size < 1024*1024*1024 {
		return fr(float64(size)/(1024*1024), 2) + "MB"
	} else if size < 1024*1024*1024*1024 {
		return fr(float64(size)/(1024*1024*1024), 2) + "GB"
	} else if size < 1024*1024*1024*1024*1024 {
		return fr(float64(size)/(1024*1024*1024*1024), 2) + "TB"
	} else if size < 1024*1024*1024*1024*1024*1024 {
		return fr(float64(size)/(1024*1024*1024*1024*1024), 2) + "PB"
	} else {
		return fr(float64(size)/(1024*1024*1024*1024*1024*1024), 2) + "EB"
	}
}

func ts(t time.Time) string {
	return t.Format(time.RFC3339)
}

func st(s string) (t time.Time) {
	t, _ = time.Parse(time.RFC3339, s)
	return t
}

func tn() time.Time {
	return time.Now()
}

func tns() s {
	return time.Now().Format(time.RFC3339)
}

type Signed interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64 | ~float32 | ~float64
}

type Unsigned interface {
	~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

type Integer interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64 | ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

type Number interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64 | ~float32 | ~float64 | ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

type Sortable interface {
	~string | ~int | ~int8 | ~int16 | ~int32 | ~int64 | ~float32 | ~float64 | ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

// int value occupy bits;
func ivbits(size I) I {
	if size == 0 {
		return 0
	}
	return I(math.Ceil(math.Log2(float64(size))))
}

// int64 value occupy bits;
func dvbits(size d) d {
	if size == 0 {
		return 0
	}
	return d(math.Ceil(math.Log2(float64(size))))
}

// uint64 value occupy bits;
func uvbits(size u) u {
	if size == 0 {
		return 0
	}
	return u(math.Ceil(math.Log2(float64(size))))
}

func vbitst[A Number](size A) A {
	if size == 0 {
		return 0
	}
	return A(math.Ceil(math.Log2(float64(size))))
}

func numstept[A Number](size, maxstep A) A {
	return A(numstep(u(size), u(maxstep)))
}

// value step ceilling value;
func numstep(size, maxstep uint64) uint64 {
	/*
	   256kb-512	1024 2048 4096 8192 16384 32768 65536 131076   256KB 512KB   1MB      2MB
	   512-8			2         4        8       16      32       64       128      256        512         1024      2048   4096
	                        512  512    512   512    512     512     512      512        512    8开始到512 3500个   8开始到4KB 5000个
	*/
	if maxstep == 0 {
		maxstep = 4096
	}
	sizbitcnt := uvbits(size)
	switch sizbitcnt {
	case 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13:
		if size%8 == 0 {
			return size
		} else {
			return size + 8 - size%8
		}
	case 14:
		if size%16 == 0 {
			return size
		} else {
			return size + 16 - size%16
		}
	case 15:
		if size%32 == 0 {
			return size
		} else {
			return size + 32 - size%32
		}
	case 16:
		if size%64 == 0 {
			return size
		} else {
			return size + 64 - size%64
		}
	case 17:
		if size%128 == 0 {
			return size
		} else {
			return size + 128 - size%128
		}
	case 18:
		if size%256 == 0 {
			return size
		} else {
			return size + 256 - size%256
		}
	case 19:
		if size%512 == 0 {
			return size
		} else {
			return size + 512 - size%512
		}
	case 20:
		if maxstep < 1024 {
			if size%maxstep == 0 {
				return size
			} else {
				return size + maxstep - size%maxstep
			}
		} else {
			if size%1024 == 0 {
				return size
			} else {
				return size + 1024 - size%1024
			}
		}
	case 21:
		if maxstep < 2048 {
			if size%maxstep == 0 {
				return size
			} else {
				return size + maxstep - size%maxstep
			}
		} else {
			if size%2048 == 0 {
				return size
			} else {
				return size + 2048 - size%2048
			}
		}
	case 22:
		if maxstep < 4096 {
			if size%maxstep == 0 {
				return size
			} else {
				return size + maxstep - size%maxstep
			}
		} else {
			if size%4096 == 0 {
				return size
			} else {
				return size + 4096 - size%4096
			}
		}
	case 23:
		if maxstep < 8192 {
			if size%maxstep == 0 {
				return size
			} else {
				return size + maxstep - size%maxstep
			}
		} else {
			if size%8192 == 0 {
				return size
			} else {
				return size + 8192 - size%8192
			}
		}
	case 24:
		if maxstep < 16384 {
			if size%maxstep == 0 {
				return size
			} else {
				return size + maxstep - size%maxstep
			}
		} else {
			if size%16384 == 0 {
				return size
			} else {
				return size + 16384 - size%16384
			}
		}
	default:
		if size%maxstep == 0 {
			return size
		} else {
			return size + maxstep - size%maxstep
		}
	}
}

func clo(bs []byte) []byte {
	bs2 := make([]byte, numstept[int](len(bs), 512))
	copy(bs2, bs)
	bs2 = bs2[:len(bs)]
	return bs2
}

func zfill(b []byte, c byte) []byte {
	for i := 0; i < len(b); i += 1 {
		b[i] = c
	}
	return b
}

// bytes to zero from bitpos;
func zzero(b []byte, bitpos int64) []byte {
	b[bitpos/8] &= ^uint8(0) << (8 - bitpos%8)
	for i := bitpos/8 + 1; i < dl(b); i += 1 {
		b[i] = 0
	}
	return b
}

func dl(b any) int64 {
	return d(reflect.ValueOf(b).Len())
}

func ul(b any) int64 {
	return d(reflect.ValueOf(b).Len())
}

// integer divide ceiling;
func idc(u, b int) int {
	if u%b == 0 {
		return u / b
	} else {
		return u/b + 1
	}
}

// integer divisor max for 0 remainder;
func idrma(u, b int) int {
	if u%b == 0 {
		return u
	} else {
		return (u/b + 1) * b
	}
}

// integer divide ceiling;
func ddc(u, b int64) int64 {
	if u%b == 0 {
		return u / b
	} else {
		return u/b + 1
	}
}

// integer divisor max for 0 remainder;
func ddrma(u, b int64) int64 {
	if u%b == 0 {
		return u
	} else {
		return (u/b + 1) * b
	}
}

// integer divide ceiling;
func udc(u, b uint64) uint64 {
	if u%b == 0 {
		return u / b
	} else {
		return u/b + 1
	}
}

// integer divisor max for 0 remainder;
func udrma(u, b uint64) uint64 {
	if u%b == 0 {
		return u
	} else {
		return (u/b + 1) * b
	}
}

// is number
func inr(b byte) bool {
	if b >= '0' && b <= '9' {
		return true
	}
	return false
}

// is alpha
func iaa(b byte) bool {
	if b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' {
		return true
	}
	return false
}

// is lower
func ilr(b byte) bool {
	if b >= 'a' && b <= 'z' {
		return true
	}
	return false
}

// is upper
func iur(b byte) bool {
	if b >= 'A' && b <= 'Z' {
		return true
	}
	return false
}

// is punct
func ipt(b byte) bool {
	if b >= ' ' && b < 127 && !(b >= '0' && b <= '9' || b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z') {
		return true
	}
	return false
}

// is alpha number
func ian(b byte) bool {
	if !(b >= '0' && b <= '9' || b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z') {
		return false
	}
	return true
}

// is number for []byte string;
func inra(bss any) bool {
	var bs z
	switch bss.(type) {
	case string:
		bs = z(bss.(s))
	case []byte:
		bs = bss.(z)
	default:
		E("type error")
	}
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= '0' && b <= '9') {
			return false
		}
	}
	return true
}

// is bytes alphass;
func ias(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z') {
			return false
		}
	}
	return true
}

// is bytes alphass;
func ins(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= '0' && b <= '9') {
			return false
		}
	}
	return true
}

// is lower
func ils(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= 'a' && b <= 'z') {
			return true
		}
	}
	return false
}

// is upper
func ius(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= 'A' && b <= 'Z') {
			return false
		}
	}
	return true
}

// is bytes puncts
func ips(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= ' ' && b < 127 && !(b >= '0' && b <= '9' || b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z')) {
			return false
		}
	}
	return true
}

// is bytes alphas merge numbers;
func ians(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= '0' && b <= '9' || b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z') {
			return false
		}
	}
	return true
}

// is bytes hex;
func ihs(bs []byte) bool {
	if len(bs) == 0 {
		return false
	}
	for _, b := range bs {
		if !(b >= '0' && b <= '9' || b >= 'a' && b <= 'f' || b >= 'A' && b <= 'F') {
			return false
		}
	}
	return true
}

// any to int;
func a2i(a any) int {
	var s string
	switch a.(type) {
	case []byte:
		s = string(a.([]byte))
	case string:
		s = string(a.(string))
	default:
		E("type error")
	}
	i := 0
	if s[i] == '-' || s[i] == '+' {
		i += 1
		if i < len(s) && !(s[i+1] >= '0' && s[i+1] <= '9') {
			return 0
		}
	}
	for ; i < len(s); i++ {
		if !(s[i] >= '0' && s[i] <= '9') {
			if s[i] == '.' {
				i += 1
				if s[i] >= '0' && s[i] <= '9' {
					for ; i < len(s); i++ {
						if !(s[i] >= '0' && s[i] <= '9') {
							break
						}
					}
				} else {
					i -= 1
				}
			}
			if s[i] == 'e' || s[i] == 'E' {
				i += 1
				if s[i] == '-' || s[i] == '+' {
					i += 1
				}
				if s[i] >= '0' && s[i] <= '9' {
					for ; i < len(s); i++ {
						if !(s[i] >= '0' && s[i] <= '9') {
							break
						}
					}
				} else {
					i -= 1
					if s[i] == '-' || s[i] == '+' {
						i -= 1
					}
				}
			}
			break
		}
	}
	P(s[:i])
	if strings.Index(s[:i], "e") == -1 && strings.Index(s[:i], "E") == -1 {
		i64, i64e := strconv.ParseInt(s[:i], 10, 64)
		if i64e == nil {
			return int(i64)
		}
	} else {
		f64, f64e := strconv.ParseFloat(s[:i], 64)
		if f64e == nil {
			return int(f64)
		}
	}
	return 0
}

func i2a(v int) string {
	return strconv.FormatInt(int64(v), 10)
}

// any to uint;
func a2u(a any) uint {
	var s string
	switch a.(type) {
	case []byte:
		s = string(a.([]byte))
	case string:
		s = string(a.(string))
	default:
		E("type error")
	}
	i := 0
	for ; i < len(s); i++ {
		if !(s[i] >= '0' && s[i] <= '9') {
			if s[i] == '.' {
				i += 1
				if s[i] >= '0' && s[i] <= '9' {
					for ; i < len(s); i++ {
						if !(s[i] >= '0' && s[i] <= '9') {
							break
						}
					}
				} else {
					i -= 1
				}
			}
			if s[i] == 'e' || s[i] == 'E' {
				i += 1
				if s[i] == '-' || s[i] == '+' {
					i += 1
				}
				if s[i] >= '0' && s[i] <= '9' {
					for ; i < len(s); i++ {
						if !(s[i] >= '0' && s[i] <= '9') {
							break
						}
					}
				} else {
					i -= 1
					if s[i] == '-' || s[i] == '+' {
						i -= 1
					}
				}
			}
			break
		}
	}
	if strings.Index(s[:i], "e") == -1 && strings.Index(s[:i], "E") == -1 {
		u64, u64e := strconv.ParseUint(s[:i], 10, 64)
		if u64e == nil {
			return uint(u64)
		}
	} else {
		f64, f64e := strconv.ParseFloat(s[:i], 64)
		if f64e == nil {
			return uint(f64)
		}
	}
	return 0
}

func u2a(v uint) string {
	return strconv.FormatUint(uint64(v), 10)
}

func zf(k z) float64 {
	return math.Float64frombits(binary.BigEndian.Uint64(k[:8]))
}

func zf4(k z) float32 {
	return math.Float32frombits(binary.BigEndian.Uint32(k[:4]))
}

func fz(f float64, buf ...z) z {
	if len(buf) == 0 {
		buf = append(buf, make(z, 8))
	}
	fu := math.Float64bits(f)
	binary.BigEndian.PutUint64(buf[0][:8], fu)
	return buf[0]
}

func f4z(f float32, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, 4))
	}
	fu := math.Float32bits(f)
	binary.BigEndian.PutUint32(buf[0][:4], fu)
	return buf[0]
}

func zd(k z) int64 {
	return d(binary.BigEndian.Uint64(k[:8]))
}

func zd4(k z) int32 {
	return d4(binary.BigEndian.Uint32(k[:4]))
}
func zd2(k z) int16 {
	return d2(binary.BigEndian.Uint16(k[:2]))
}

func dz(d8 int64, buf ...z) z {
	if len(buf) == 0 {
		buf = append(buf, make(z, 8))
	}
	binary.BigEndian.PutUint64(buf[0][:8], u(d8))
	return buf[0]
}
func d4z(d4 int32, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, 4))
	}
	binary.BigEndian.PutUint32(buf[0][:4], u4(d4))
	return buf[0]
}

func d2z(d2 int16, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, 2))
	}
	binary.BigEndian.PutUint16(buf[0][:2], u2(d2))
	return buf[0]
}

func zu(k z) uint64 {
	return u(binary.BigEndian.Uint64(k[:8]))
}

func zu4(k z) uint32 {
	return u4(binary.BigEndian.Uint32(k[:4]))
}

func zu2(k z) uint16 {
	return u2(binary.BigEndian.Uint16(k[:2]))
}

func uz(d8 uint64, buf ...z) z {
	if len(buf) == 0 {
		buf = append(buf, make(z, 8))
	}
	binary.BigEndian.PutUint64(buf[0][:8], u(d8))
	return buf[0]
}

func u4z(d4 uint32, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, 4))
	}
	binary.BigEndian.PutUint32(buf[0][:4], u4(d4))
	return buf[0]
}

func u2z(d2 uint16, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, 2))
	}
	binary.BigEndian.PutUint16(buf[0][:2], u2(d2))
	return buf[0]
}

func zI(k z) int {
	switch unsafe.Sizeof([1]int{}) {
	case 4:
		return I(binary.BigEndian.Uint32(k[:4]))
	case 8:
		return I(binary.BigEndian.Uint64(k[:8]))
	default:
		E("unknown int size")
	}
	return 0
}

func Iz(iv int, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, unsafe.Sizeof([1]int{})))
	}
	switch unsafe.Sizeof([1]int{}) {
	case 4:
		binary.BigEndian.PutUint32(buf[0], u4(iv))
		return buf[0][:4]
	case 8:
		binary.BigEndian.PutUint64(buf[0], u(iv))
		return buf[0][:8]
	default:
		E("unknown int size")
	}
	return nil

}

func zU(k z) uint {
	switch unsafe.Sizeof([1]uint{}) {
	case 4:
		return U(binary.BigEndian.Uint32(k[:4]))
	case 8:
		return U(binary.BigEndian.Uint64(k[:8]))
	default:
		E("unknown int size")
	}
	return 0
}

func Uz(iv uint, buf ...z) z {
	if buf == nil {
		buf = append(buf, make(z, unsafe.Sizeof([1]uint{})))
	}
	switch unsafe.Sizeof([1]uint{}) {
	case 4:
		binary.BigEndian.PutUint32(buf[0], u4(iv))
		return buf[0][:4]
	case 8:
		binary.BigEndian.PutUint64(buf[0], u(iv))
		return buf[0][:8]
	default:
		E("unknown int size")
	}
	return nil
}

// any to float64;
func a2f(a any) (v float64) {
	var s string
	switch a.(type) {
	case []byte:
		s = string(a.([]byte))
	case string:
		s = string(a.(string))
	default:
		E("type error")
	}
	i := 0
	if s[i] == '-' || s[i] == '+' {
		i += 1
		if i < len(s) && !(s[i+1] >= '0' && s[i+1] <= '9') {
			return 0
		}
	}
	for ; i < len(s); i++ {
		if !(s[i] >= '0' && s[i] <= '9') {
			if s[i] == '.' {
				i += 1
				if i < len(s) && s[i] >= '0' && s[i] <= '9' {
					for ; i < len(s) && s[i] >= '0' && s[i] <= '9'; i++ {
					}
				} else {
					i -= 1
				}
			}
			if i < len(s) && (s[i] == 'e' || s[i] == 'E') {
				i += 1
				if s[i] == '-' || s[i] == '+' {
					i += 1
				}
				if s[i] >= '0' && s[i] <= '9' {
					for ; i < len(s) && s[i] >= '0' && s[i] <= '9'; i++ {
					}
				} else {
					i -= 1
					if s[i] == '-' || s[i] == '+' {
						i -= 1
					}
				}
			}
			break
		}
	}
	P(s[:i])
	f64, f64e := strconv.ParseFloat(s[:i], 64)
	if f64e == nil {
		return f64
	}
	return 0
}

func f2a(v float64) string {
	return strconv.FormatFloat(v, 'g', 15, 64)
}

func abs[T Signed](a T) T {
	if a < 0 {
		return -a
	}
	return a
}

func fnt() string {
	return time.Now().Format("20060102T150405")
}

func zgua[A Number](b []byte, start, end A) (val A) {
	return A(zgu(b, u(start), u(end)))
}

// bytes get uint64; 0 from b left to right
func zgu(b []byte, start, end uint64) (val uint64) {
	n := start / 8
	if start%8 == 0 {
		n2 := (end - start) / 8
		for i := uint64(0); i < n2; i += 1 {
			val = val<<8 | uint64(b[n+i])
		}
		if end%8 != 0 {
			val = val<<((end-start)%8) | uint64(b[n+n2]>>(int(end-start)%8))
		}
		return val
	} else {
		lsiz := 8 - start%8
		if end-start < lsiz {
			lsiz = end - start
			return u(b[n]<<start%8) >> (8 - (start%8 + lsiz))
		} else {
			val = uint64((b[n] << (8 - lsiz)) >> lsiz)
		}
		n2 := ((end - start) - lsiz) / 8
		for i := uint64(0); i < n2; i += 1 {
			val = val<<8 | uint64(b[n+i+1])
		}
		if end%8 != 0 {
			if ((end-start)-lsiz)%8 >= 0 {
				val = val<<(((end-start)-lsiz)%8) | uint64(b[n+n2+1]>>(int((end-start)-lsiz)%8))
			}
		}
		return val
	}
}

// bytes set uint64;
func zsua[A Number](b []byte, start, end, val A) error {
	return zsu(b, u(start), u(end), u(val))
}
func zsu(b []byte, start, end, val uint64) error {
	n := start / 8
	if start%8 != 0 {
		scnt := 8 - start%8
		if end-start < scnt {
			scnt = end - start
		}
		if end-start <= 8 && end < start+(8-start%8) {
			b[n] = bms(b[n], int(start%8), int(end%8-start%8), byte(val))
			return nil
		}
		b[n] = brs(b[n], int(scnt), byte(val>>(end-start-scnt)))
		n2 := (end - start - (8 - start%8)) / 8
		for i := u0; i < n2; i += 1 {
			b[n+i+1] = byte(val >> ((end - start) - (scnt + i*8) - 8))
		}
		if (end-start-scnt)%8 != 0 {
			m := n + n2 + 1
			if ((end-start)-(8-start%8))%8 >= 0 {
				b[m] = bls(b[m], int(end-start-scnt)%8, byte(val))
			}
		}
		return nil
	} else {
		n2 := (end - start) / 8
		for i := u0; i < n2; i += 1 {
			b[n+i] = byte(val >> ((end - start) - i*8 - 8))
		}
		if end%8 != 0 {
			m := n + n2
			mv := 8 - start%8
			if mv == 8 {
				mv = 0
			}
			b[m] = bls(b[m], int((end-start)-mv)%8, byte(val))
		}
		return nil
	}
}

// byte ledt set value;
func bls(ob byte, vbn int, lb byte) byte {
	return ob&((1<<(8-vbn))-1) | lb<<(8-vbn)
}

// byte ledt get value;
func blg(ob byte, vbn int) byte {
	return ob >> (8 - vbn)
}

// byte right set value;
func brs(ob byte, vbn int, v byte) byte {
	return ob&(((1<<(8-vbn))-1)<<vbn) | v
}

// byte right get value;
func brg(ob byte, vbn int) byte {
	return ob << (8 - vbn) >> (8 - vbn)
}

// byte middle set value;
func bms(ob byte, st, vbn int, v byte) byte {
	return ob&^(((1<<vbn)-1)<<(8-st-vbn)) | v<<(8-st-vbn)
}

// byte middle get value;
func bmg(ob byte, st, vbn int) byte {
	return ob & (((1 << vbn) - 1) << (8 - st - vbn))
}

// uint64 ledt set value;
func uls(ob uint64, vbn int, lb u) uint64 {
	return ob&((1<<(64-vbn))-1) | lb<<(64-vbn)
}

// uint64 ledt get value;
func ulg(ob uint64, vbn int) uint64 {
	return ob >> (8 - vbn)
}

// uint64 right set value;
func urs(ob uint64, vbn int, v u) u {
	return ob&(((1<<(64-vbn))-1)<<vbn) | v
}

// uint64 right get value;
func urg(ob uint64, vbn int) u {
	return ob << (64 - vbn) >> (64 - vbn)
}

// uint64 middle set value;
func ums(ob u, st, vbn int, v u) u {
	return ob&^(((1<<vbn)-1)<<(64-st-vbn)) | v<<(64-st-vbn)
}

// uint64 middle get value;
func umg(ob u, st, vbn int) u {
	return ob & (((1 << vbn) - 1) << (64 - st - vbn))
}

func mof(path string) (of *os.File) {
	var ofe error
	of, ofe = os.OpenFile(path, os.O_CREATE|os.O_WRONLY, 0666)
	if ofe != nil {
		P(ofe)
	}
	return of
}

func nof(path string) (of *os.File) {
	var ofe error
	of, ofe = os.OpenFile(path, os.O_TRUNC|os.O_CREATE|os.O_WRONLY, 0666)
	if ofe != nil {
		P(ofe)
	}
	return of
}

// string split by seporater;
func ssp(s0, sep s) []s {
	return strings.Split(s0, sep)
}

// string find replace replace string;
func sr(s0, sf, sr s) s {
	return strings.Replace(s0, sf, sr, -1)
}

// string regex replace all by string;
func srs(s0, frx, sr s) s {
	return regexp.MustCompile(frx).ReplaceAllString(s0, sr)
}

// string regex find a string;
func srg(s0, frx s) s {
	return regexp.MustCompile(frx).FindString(s0)
}

// string regex find all strings;
func srfa(s0, frx s) []s {
	return regexp.MustCompile(frx).FindAllString(s0, -1)
}

// string replace by express #1 #2...;
func sre(source, find, repw string) s {
	return s(zre(z(source), find, repw))
}

// trim
func tri(s0, v s) s {
	return strings.Trim(s0, v)
}

// trim right
func trr(s0, v s) s {
	return strings.TrimRight(s0, v)
}

// trim left;
func trl(s0, v s) s {
	return strings.TrimLeft(s0, v)
}

// trim space;
func trs(s0 s) s {
	return strings.Trim(s0, " \r\n\t")
}

// bytes regex find replace by expression #0 #1...;
func zre(source []byte, find, repw string) []byte {
	ls := []string{}
	tm := []byte{}
	for ri := 0; ri < len(repw); ri += 1 {
		if ri+3 < len(repw) && repw[ri] == '\\' && repw[ri+1] == 'x' && (repw[ri+2] >= '0' && repw[ri+2] <= '9' || repw[ri+2] >= 'a' && repw[ri+2] <= 'f' || repw[ri+2] >= 'A' && repw[ri+2] <= 'F') && (repw[ri+3] >= '0' && repw[ri+3] <= '9' || repw[ri+3] >= 'a' && repw[ri+3] <= 'f' || repw[ri+3] >= 'A' && repw[ri+3] <= 'F') {
			v64, v64e := strconv.ParseUint(repw[ri+2:ri+2+2], 16, 8)
			if v64e == nil {
				tm = append(tm, byte(v64))
			}
			ri += 2
		} else if ri+1 < len(repw) && repw[ri] == '\\' && (repw[ri+1] >= '0' && repw[ri+1] <= '9' || repw[ri+1] == '\\' || repw[ri+1] == '#' || repw[ri+1] == '%' || repw[ri+1] == 'n' || repw[ri+1] == 'r' || repw[ri+1] == 't') {
			if repw[ri+1] >= '0' && repw[ri+1] <= '9' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, repw[ri+1:ri+2])
				ri += 1
			} else if repw[ri+1] == 'n' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, "\n")
				ri += 1
			} else if repw[ri+1] == 'r' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, "\r")
				ri += 1
			} else if repw[ri+1] == 't' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, "\t")
				ri += 1
			} else if repw[ri+1] == '\\' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, "\\")
				ri += 1
			} else if repw[ri+1] == '%' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, "%")
				ri += 1
			} else if repw[ri+1] == '#' {
				if len(tm) > 0 {
					ls = append(ls, string(tm))
					tm = tm[:0]
				}
				ls = append(ls, "#")
				ri += 1
			} else {
				tm = append(tm, '\\')
			}

		} else if ri+2 < len(repw) && repw[ri] == '#' && repw[ri+1] >= '0' && repw[ri+1] <= '9' && repw[ri+2] >= '0' && repw[ri+2] <= '9' {
			if len(tm) > 0 {
				ls = append(ls, string(tm))
				tm = tm[:0]
			}
			matag := repw[ri : ri+3]
			ls = append(ls, matag)
			ri += 2
		} else if ri+1 < len(repw) && repw[ri] == '#' && repw[ri+1] >= '0' {
			if len(tm) > 0 {
				ls = append(ls, string(tm))
				tm = tm[:0]
			}
			matag := repw[ri : ri+2]
			ls = append(ls, matag)
			ri += 1
		} else {
			tm = append(tm, repw[ri])
		}
	}
	if len(tm) > 0 {
		ls = append(ls, string(tm))
		tm = tm[:0]
	}
	rls := ls
	re, ree := regexp.Compile(find)
	if ree != nil {
		return source
	}
	gma := re.FindIndex(source)
	var newpath []byte
	for _, rl := range rls {
		if len(rl) == 3 && rl[0] == '#' && rl[1] >= '0' && rl[1] <= '9' && rl[2] >= '0' && rl[2] <= '9' {
			maind := sI(rl[1:])
			if 2*maind >= len(gma) {
				newpath = append(newpath, []byte(rl)...)
			} else {
				mastr := source[gma[2*maind]:gma[2*maind+1]]
				newpath = append(newpath, []byte(mastr)...)
			}
		} else if len(rl) == 2 && rl[0] == '#' && rl[1] >= '0' && rl[1] <= '9' {
			maind := sI(rl[1:])
			if 2*maind >= len(gma) {
				newpath = append(newpath, []byte(rl)...)
			} else {
				mastr := source[gma[2*maind]:gma[2*maind+1]]
				newpath = append(newpath, []byte(mastr)...)
			}
		} else {
			newpath = append(newpath, []byte(rl)...)
		}
	}
	if len(newpath) == 0 {
		return source
	} else {
		return newpath
	}
}

// string index;
func si(s0, sf s) I {
	return strings.Index(s0, sf)
}

// string last index;
func sli(s0, sf s) I {
	return strings.LastIndex(s0, sf)
}

// string index any;
func sia(s0, sf s) I {
	return strings.IndexAny(s0, sf)
}

// string last index any;
func sla(s0, sf s) I {
	return strings.LastIndexAny(s0, sf)
}

// is string prefix with;
func isp(s0, sf s) bool {
	return strings.HasPrefix(s0, sf)
}

// is string suffix with;
func iss(s0, sf s) bool {
	return strings.HasSuffix(s0, sf)
}

// string to low;
func slow(s0 s) s {
	return strings.ToLower(s0)
}

// string to upper;
func supp(s0 s) s {
	return strings.ToUpper(s0)
}

// bytes find replace;
func zr(s0, sf, sr z) z {
	return bytes.Replace(s0, sf, sr, -1)
}

// bytes regex find replace bytes;
func zrz(s0 z, frx s, sr z) z {
	return regexp.MustCompile(string(frx)).ReplaceAll(s0, sr)
}

// bytes index bytes;
func zi(s0, sf z) I {
	return bytes.Index(s0, sf)
}

// bytes last index bytes;
func zli(s0, sf z) I {
	return bytes.LastIndex(s0, sf)
}

// bytes index any string;
func zia(s0 z, sf s) I {
	return bytes.IndexAny(s0, sf)
}

// bytes last index any string;
func zlia(s0 z, sf s) I {
	return bytes.LastIndexAny(s0, sf)
}

// file append data;
func fa(filepath string, data []byte) error {
	ff, ffe := os.OpenFile(filepath, os.O_CREATE|os.O_WRONLY, 0666)
	if ffe != nil {
		return ffe
	}
	defer ff.Close()
	_, e2 := ff.Seek(0, os.SEEK_END)
	if e2 != nil {
		return e2
	}
	_, e := ff.Write(data)
	if e != nil {
		return e
	}
	return nil
}

// boolean any to string;
func bas(b any) string {
	switch b.(type) {
	case bool:
		if b.(bool) {
			return "true"
		} else {
			return "false"
		}
	case int:
		if b.(int) != 0 {
			return "true"
		} else {
			return "false"
		}
	case int8:
		if b.(int8) != 0 {
			return "true"
		} else {
			return "false"
		}
	case int16:
		if b.(int16) != 0 {
			return "true"
		} else {
			return "false"
		}
	case int32:
		if b.(int32) != 0 {
			return "true"
		} else {
			return "false"
		}
	case int64:
		if b.(int64) != 0 {
			return "true"
		} else {
			return "false"
		}

	case uint:
		if b.(uint) != 0 {
			return "true"
		} else {
			return "false"
		}
	case uint8:
		if b.(uint8) != 0 {
			return "true"
		} else {
			return "false"
		}
	case uint16:
		if b.(uint16) != 0 {
			return "true"
		} else {
			return "false"
		}
	case uint32:
		if b.(uint32) != 0 {
			return "true"
		} else {
			return "false"
		}
	case uint64:
		if b.(uint64) != 0 {
			return "true"
		} else {
			return "false"
		}
	case string:
		if b.(string) == "false" || b.(string) == "0" || b.(string) == "" {
			return "false"
		} else {
			return "true"
		}
	case []byte:
		if s(b.(z)) == "false" || s(b.(z)) == "0" || s(b.(z)) == "" {
			return "false"
		} else {
			return "true"
		}
	default:
		E("type error")
	}
	return "false"
}

// string to bool;
func sbn(s0 s) bool {
	if s0 == "false" || s0 == "0" || s0 == "" {
		return false
	} else {
		return true
	}
}

// encode flate compress;
func enflate(src []byte, level int, outbuf []byte) []byte {
	b := bytes.NewBuffer(outbuf)
	b.Reset()
	zw, err := flate.NewWriter(b, level)
	if err != nil {
		E("enflate error", err)
	}
	zw.Write(src)
	zw.Close()
	return b.Bytes()
}

// decode flate compress;
func deflate(src, outbuf []byte) []byte {
	if len(src) == 0 {
		return []byte{}
	}
	b := bytes.NewBuffer(src)
	zr := flate.NewReader(nil)
	if err := zr.(flate.Resetter).Reset(b, nil); err != nil {
		E("deflate error", err)
	}
	b2 := bytes.NewBuffer(outbuf)
	b2.Reset()
	outw := bufio.NewWriter(b2)
	if _, err := io.Copy(outw, zr); err != nil {
		E("deflate rror", err)
	}
	if err := zr.Close(); err != nil {
		E("deflate error", err)
	}
	return b2.Bytes()
}

func rnds(min, max int) (outs string) {
	sublen := min + rand.Intn(max-min+1)
	outbs := make([]byte, 0, sublen)
	for i := 0; i < sublen; i++ {
		outbs = append(outbs, byte(32+rand.Intn(127-32)))
	}
	return string(outbs)
}

func rndz(min, max int, buf []byte) (outbt []byte) {
	zb := bytes.NewBuffer(buf)
	size := min + rand.Intn(max-min)
	for i := min; i < size; i++ {
		zb.WriteByte(byte(rand.Intn(256)))
	}
	return zb.Bytes()
}

// bytes to hex;
func zh(bs []byte) string {
	return hex.EncodeToString(bs)
}

func now() time.Time {
	return time.Now()
}

func ofc(path string) (of *os.File, er error) {
	var ofe error
	of, ofe = os.OpenFile(path, os.O_CREATE|os.O_WRONLY, 0666)
	if ofe != nil {
		return nil, ofe
	}
	return of, nil
}

func oft(path string) (of *os.File, er error) {
	var ofe error
	of, ofe = os.OpenFile(path, os.O_TRUNC|os.O_CREATE|os.O_WRONLY, 0666)
	if ofe != nil {
		return nil, ofe
	}
	return of, nil
}

func ofm(path string) (of *os.File) {
	var ofe error
	of, ofe = os.OpenFile(path, os.O_CREATE|os.O_WRONLY, 0666)
	if ofe != nil {
		return nil
	}
	return of
}

func cmpt[A Sortable](a, b A) int {
	if a < b {
		return -1
	} else if a > b {
		return 1
	} else {
		return 0
	}
}

// any number to float64 bytes
func anfz(v any, buf ...z) (fz []byte) {
	if len(buf) > 0 {
		fz = buf[0]
	} else {
		fz = make([]byte, 8)
	}
	switch v.(type) {
	case uint8:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(uint8))))
	case uint16:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(uint16))))
	case uint32:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(uint32))))
	case uint64:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(uint64))))
	case int8:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(int8))))
	case int16:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(int16))))
	case int32:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(int32))))
	case int64:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(int64))))
	case int:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(int))))
	case uint:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(uint))))
	case float32:
		binary.BigEndian.PutUint64(fz, math.Float64bits(float64(v.(float32))))
	case float64:
		binary.BigEndian.PutUint64(fz, math.Float64bits(v.(float64)))
	case []byte:
		ff := sf(string(v.([]byte)))
		binary.BigEndian.PutUint64(fz, math.Float64bits(ff))
	case string:
		ff := sf(v.(string))
		binary.BigEndian.PutUint64(fz, math.Float64bits(ff))
	default:
		E("type error", reflect.TypeOf(v).String())
	}
	return fz
}

// any number to string
func anfs(v any) (fs s) {
	switch v.(type) {
	case uint8:
		return fmt.Sprintf("%d", v.(uint8))
	case uint16:
		return fmt.Sprintf("%d", v.(uint16))
	case uint32:
		return fmt.Sprintf("%d", v.(uint32))
	case uint64:
		return fmt.Sprintf("%d", v.(uint64))
	case int8:
		return fmt.Sprintf("%d", v.(int8))
	case int16:
		return fmt.Sprintf("%d", v.(int16))
	case int32:
		return fmt.Sprintf("%d", v.(int8))
	case int64:
		return fmt.Sprintf("%d", v.(int64))
	case int:
		return fmt.Sprintf("%d", v.(int))
	case uint:
		return fmt.Sprintf("%d", v.(uint))
	case float32:
		return fmt.Sprintf("%g", v.(float32))
	case float64:
		return fmt.Sprintf("%g", v.(float64))
	case []byte:
		return string(v.([]byte))
	case string:
		return v.(string)
	default:
		E("type error", reflect.TypeOf(v).String())
	}
	return "0"
}
