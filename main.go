package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/md5"
	"encoding/base64"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"math/rand"
	"net/url"
	"os"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/go-irc/irc"
	"github.com/signal-golang/textsecure"
)

var storageDir = ".storage"
var storagePasswd = ""
var authSalt = ""

func run() error {
	flag.StringVar(&storageDir, "storagedir", storageDir, "Storage directory")
	flag.StringVar(&storagePasswd, "storagepasswd", storagePasswd, "Storage password (or from env SIGNAL_STORAGE_PASSWD if not set)")
	flag.StringVar(&authSalt, "authsalt", authSalt, "Auth salt (or from env BRIDGE_AUTH_SALT if not set)")
	flag.Parse()

	if storagePasswd == "" {
		storagePasswd = os.Getenv("SIGNAL_STORAGE_PASSWD")
	}
	if authSalt == "" {
		authSalt = os.Getenv("BRIDGE_AUTH_SALT")
	}

	if storageDir == "" {
		return errors.New("storage directory not set")
	}
	if storagePasswd == "" {
		return errors.New("storage password not set")
	}
	if authSalt == "" {
		return errors.New("auth salt not set")
	}

	type stdio struct {
		io.Reader
		io.WriteCloser
	}
	conn := &stdio{os.Stdin, os.Stdout}

	c := &client{
		conn: conn,
	}
	ctx := context.WithValue(context.Background(), clientKey, c)
	c.connected(ctx)

	scan := bufio.NewScanner(conn)
	scan.Split(scanNewlineTerm)
	for scan.Scan() {
		line := scan.Bytes()
		if err := c.handleLine(ctx, line); err != nil {
			c.stop(ctx)
			time.Sleep(200 * time.Millisecond)
			return err
		}
	}
	return scan.Err()
}

type msgInfo struct {
	raw     string
	rawType string // "text/x-irc" if IRC formatting, otherwise "text/plain"
	plain   string // Plain text version of raw.
}

var clients = map[string]*client{} // key=tel, locked by mx
var mx sync.Mutex

// Returns false if the client (tel) already exists!
func addClient(c *client) bool {
	mx.Lock()
	defer mx.Unlock()
	if _, ok := clients[c.tel]; ok {
		return false
	}
	clients[c.tel] = c
	return true
}

func removeClient(c *client) {
	mx.Lock()
	defer mx.Unlock()
	delete(clients, c.tel)
}

type ctxKey struct{ s string }

var clientKey = &ctxKey{"client"}

const ServerName = "signal.bridge"
const VerifyName = "*VerifySignal"
const NetworkName = "Signal"

var capsSupported = []string{} // []string{"extended-join", "account-notify"}

type client struct {
	tel         string // "+1771111001"
	nick        string
	nickAtomic  atomic.Value // string with nick
	conn        io.ReadWriteCloser
	mx          sync.Mutex // used for sending on conn
	tsleep      time.Duration
	verifyChan  chan string
	err         error
	batchTarget string
	//batchTag    string
	batchMsg    strings.Builder
	tsc         *textsecure.Client // nil if not setup yet.
	capsEnabled []string
	batching    bool
}

func (c *client) connected(ctx context.Context) {
	c.capsEnabled = nil
	c.setNick("*")
}

func (c *client) hasCapEnabled(cap string) bool {
	return strInStrs(cap, c.capsEnabled)
}

// thread safe
func (c *client) getNick() string {
	nick, _ := c.nickAtomic.Load().(string)
	return nick
}

// Can only be called from main client thread!
func (c *client) setNick(newNick string) {
	c.nick = newNick
	c.nickAtomic.Store(newNick)
}

func (c *client) stop(ctx context.Context) {
	c.tscStop(ctx)
	c.connClose()
}

func (c *client) tscStop(ctx context.Context) {
	if c.tsc != nil {
		textsecure.StopListening()
		c.tsc = nil
	}
	if c.verifyChan != nil {
		ch := c.verifyChan
		c.verifyChan = nil
		close(ch)
	}
}

func (c *client) resetBatch() {
	c.batching = false
	c.batchTarget = ""
	//c.batchTag = ""
	c.batchMsg.Reset()
}

func (c *client) tsFlushBatch() {
	if c.batchMsg.Len() > 0 && c.batchTarget != "" {
		c.tsSendMsg(c.batchTarget, c.batchMsg.String())
	}
	c.resetBatch()
}

func (c *client) send(line []byte) {
	c.mx.Lock()
	defer c.mx.Unlock()
	if _, err := c.conn.Write(append(line, "\r\n"...)); err != nil {
		c.err = err
	}
}

func (c *client) sendString(line string) {
	c.mx.Lock()
	defer c.mx.Unlock()
	if _, err := c.conn.Write(append([]byte(line), "\r\n"...)); err != nil {
		c.err = err
	}
}

func (c *client) connClose() error {
	c.mx.Lock()
	defer c.mx.Unlock()
	return c.conn.Close()
}

func earg(msg *irc.Message, i int) (string, bool) {
	if i < len(msg.Params) {
		return msg.Params[i], true
	}
	return "", false
}

// Get trailing param at least at index i.
func eargTrailing(msg *irc.Message, i int) (string, bool) {
	if i < len(msg.Params) {
		return msg.Trailing(), true
	}
	return "", false
}

func (c *client) needPass(cmd string) {
	// The auth hash is the hex MD5 (lowercase) of: authSalt combined with tel.
	// So if the authSalt is "foobar" and the tel is "+1771111001" then
	// the auth hash would be "ae68d9c7ba2167f6058842978014e56d"
	c.sendString(":" + ServerName + " 464 " + cmd +
		` :Must send "PASS <tel>,<hash>[,voice]" such as "PASS +1771111001,ae68d9c7ba2167f6058842978014e56d"`)
}

func (c *client) tsSendMsg(target, message string) {
	var sendErr error
	isChan := false
	if target == "" {
		sendErr = errors.New("message has no target")
	} else if target[0] == '#' {
		isChan = true
		group := target[1:]
		_, sendErr = textsecure.SendGroupMessage(group, message, 0)
	} else {
		fromUser := target
		_, sendErr = textsecure.SendMessage(fromUser, message, 0)
	}
	if sendErr != nil {
		log.Printf("error sending from %s to %s: %v", c.tel, target, sendErr)
		num := "401" // ERR_NOSUCHNICK = "401"
		if isChan {
			num = "404" // ERR_CANNOTSENDTOCHAN = "404
		}
		c.sendString(":" + ServerName + " " + num + " " + c.nick + " " + target + " " +
			" :Unable to send message to " + target + " " + sendErr.Error())
	}
}

// https://en.wikipedia.org/wiki/Telephone_number
// "the entire number should be 15 digits or shorter"
var phoneRegexp = regexp.MustCompile(`^\+\d{10,15}$`)

// Return c.err from this, if not another error.
func (c *client) handleLine(ctx context.Context, line []byte) error {
	msg, err := irc.ParseMessage(string(line))
	if err != nil {
		if err != irc.ErrZeroLengthMessage {
			c.sendString("X :Parse error")
		}
		return c.err
	}
	anywork := true
	switch msg.Command {
	case "PASS":
		auth, _ := earg(msg, 0)
		authParts := strings.Split(auth, ",")
		if len(authParts) < 2 {
			c.needPass(msg.Command)
		} else {
			// See needPass for info on generating the auth hash.
			tel := authParts[0]
			hash := authParts[1]
			vtype := "sms"
			if !phoneRegexp.MatchString(tel) {
				c.sendString(":" + ServerName + " 464 " + c.nick + " :Invalid phone number (tel)")
				return c.err
			}
			if len(authParts) > 2 {
				vtype = authParts[2]
				if vtype != "sms" && vtype != "voice" {
					c.sendString(":" + ServerName + " 464 " + c.nick + " :Invalid verification type")
					return c.err
				}
			}
			realHashBytes := md5.Sum([]byte(tel + authSalt))
			realHash := hex.EncodeToString(realHashBytes[:])
			//log.Printf("PASS tel=`%s` hash=`%s` - realHash=`%s` authSalt=`%s`",
			//	tel, hash, realHash, authSalt)
			if hash != realHash {
				time.Sleep(time.Duration(rand.Int31n(100)) * time.Millisecond)
				c.sendString(":" + ServerName + " 464 " + c.nick + " :Password incorrect")
			} else if c.tsc != nil {
				// TODO: move this above..
				c.sendString(":" + ServerName + " 464 " + c.nick + " :Cannot auth again")
			} else {
				//c.tscStop(ctx) // Not safe?
				registeredAtomic := int32(0)
				c.verifyChan = make(chan string)
				c.tel = tel
				type ircChan struct {
					nicklist map[string]struct{} // key=lowercase nick
				}
				ircChans := make(map[string]*ircChan) // key=lowercase channel name
				tsc := &textsecure.Client{
					GetConfig: func() (*textsecure.Config, error) {
						return &textsecure.Config{
							Tel:             tel,
							StorageDir:      storageDir + "/" + tel,
							StoragePassword: storagePasswd,
							//LogLevel:        "warn",
							VerificationType: vtype,
						}, nil
					},
					MessageHandler: func(tsmsg *textsecure.Message) {
						fromUser := getNick(tsmsg)
						lfromUser := strings.ToLower(fromUser)
						fullsource := getFullAddress(tsmsg)
						target := "?"
						if tsmsg.Group() != nil {
							nick := c.getNick()     // My nick.
							isRegged := nick != "*" // Am I registered?
							group := tsmsg.Group()
							chanName := "#" + group.Hexid
							lchanName := strings.ToLower(chanName)
							target = chanName
							userInChan := false
							ichan, chanExists := ircChans[lchanName] // Stays nil/false if !isRegged
							// Note: if !isRegged we don't send JOINs yet,
							// because I can't join a channel without a nick.
							if chanExists {
								_, userInChan = ichan.nicklist[lfromUser]
							} else if isRegged {
								// I need to join...
								// TODO: use my full address.
								c.sendString(":" + nick + " JOIN " + chanName)
								ichan = &ircChan{
									nicklist: make(map[string]struct{}),
								}
								ircChans[lchanName] = ichan
							}
							if !userInChan && isRegged {
								ichan.nicklist[lfromUser] = struct{}{}
								c.sendString(":" + fullsource + " JOIN " + chanName)
								// Note: will do rapid JOIN/PART if Flags==GroupLeaveFlag.
							}
							if group.Flags == textsecure.GroupUpdateFlag {
								log.Printf("[%s] Updated the group %s", fullsource, chanName)
							} else if group.Flags == textsecure.GroupLeaveFlag {
								//log.Printf("[%s] Left the group %s", fullsource, chanName)
								if isRegged {
									c.sendString(":" + fullsource + " PART " + target)
								}
							}
						} else {
							fromUser := tsmsg.Source()
							target = fromUser
						}
						if tsmsg.Flags() == textsecure.EndSessionFlag {
							// Secure session reset.
							log.Printf("[%s] Secure session reset", fullsource)
						} else if tsmsg.Flags() == 2 {
							log.Printf("[%s] Message timer update", fullsource)
						}
						if tsmsg.Sticker() != nil {
							sticker := tsmsg.Sticker()
							stickerCodeSB := &strings.Builder{}
							enc := base64.NewEncoder(base64.RawURLEncoding, stickerCodeSB)
							enc.Write(sticker.PackId)
							stickerCodeSB.WriteByte('.')
							enc.Write(sticker.PackKey)
							if sticker.StickerId != nil {
								fmt.Fprintf(stickerCodeSB, "%d", *sticker.StickerId)
							}
							stickerCode := stickerCodeSB.String()
							//log.Printf("Sticker: %s \"%s\"", stickerCode, sticker.GetEmoji())
							emoji := strings.ReplaceAll(strings.ReplaceAll(
								sticker.GetEmoji(), "\r", " "), "\n", " ")
							/*if emoji != "" {
								m := "* Sticker: " + emoji
								c.sendString(":" + fullsource + " PRIVMSG " + target +
									" :" + m)
							}*/
							c.sendString(":" + fullsource + " PRIVMSG " + target +
								" :\x01SIGNAL-STICKER " + stickerCode +
								" " + emoji + "\x01")
						}
						for _, msgline := range strings.Split(tsmsg.Message(), "\n") {
							msgline = strings.TrimRight(msgline, "\r")
							if msgline != "" {
								c.sendString(":" + fullsource + " PRIVMSG " + target + " :" + msgline)
							}
						}
					},
					GetVerificationCode: func() string {
						c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
							" :Enter the verification code sent to " + tel + ":")
						select {
						case vcode, ok := <-c.verifyChan:
							if !ok {
								c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
									" :Cancelled")
							}
							atomic.StoreInt32(&registeredAtomic, 1)
							return vcode
						case <-time.After(30 * time.Minute):
							c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
								" :Timed out. Registration troubleshooting: https://support.signal.org/hc/en-us/articles/360007318751")
							return ""
						}
					},
					GetPin: func() string {
						c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
							" :Enter the PIN for " + tel + ":")
						select {
						case vcode, ok := <-c.verifyChan:
							if !ok {
								c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
									" :Cancelled")
							}
							return vcode
						case <-time.After(30 * time.Minute):
							c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
								" :Timed out")
							return ""
						}
					},
					RegistrationDone: func() {
						first := false
						if atomic.CompareAndSwapInt32(&registeredAtomic, 1, 2) {
							first = true
							c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
								" :Registration accepted for " + tel)
						} else if atomic.CompareAndSwapInt32(&registeredAtomic, 0, 2) {
							first = true
						}
						if first {
							c.sendString(":" + ServerName + " NOTICE " + c.getNick() +
								" :Signal online")
						}
					},
					GetLocalContacts: func() ([]textsecure.Contact, error) {
						return nil, nil
					},
				}
				c.tsc = tsc
				go func() {
					defer c.connClose()
					err := textsecure.Setup(tsc) // This hangs for the registration process!
					if err != nil {
						c.sendString("X :Error in textsecure.Setup(): " + err.Error())
						//c.tscStop(ctx) // Not thread safe.
						// Note: error can be "Rate Limit Exeded" [sic]
						return
					}
					if false {
						// Ensure this "device" linked.
						// tsdevice:/?uuid=xxx&pub_key=yyy
						devfile := storageDir + "/" + tel + ".device"
						st, err := os.Stat(devfile)
						if err != nil && !os.IsNotExist(err) {
							log.Printf("Unable to stat file %s: %+v", devfile, err)
							c.sendString("X :Unable to stat device file: " + err.Error())
						} else if st == nil {
							log.Printf("Linking new device for %s ...", tel)
							pubKeyBytes := textsecure.MyIdentityKey()
							uuidHexDashed, err := textsecure.GetMyUUID()
							if err != nil {
								uuidHexDashed = "???"
								log.Printf("textsecure.GetMyUUID() failed: %v", err)
							}
							uuidBytes, _ := hex.DecodeString(strings.ReplaceAll(uuidHexDashed, "-", ""))
							uuid := base64.RawStdEncoding.EncodeToString(uuidBytes[:])
							pubKey := base64.RawStdEncoding.EncodeToString(pubKeyBytes[:])
							deviceURL := "tsdevice:/?" + url.Values{
								"uuid":    []string{uuid},
								"pub_key": []string{pubKey}}.Encode()
							log.Printf("Linking device with URL: %v", deviceURL)
							code, err := textsecure.NewDeviceVerificationCode()
							if err != nil {
								log.Printf("textsecure.NewDeviceVerificationCode() fail: %+v", err)
								c.sendString("X :Could not register device: " + err.Error())
							} else {
								if err := textsecure.AddDevice(uuid, pubKey, code); err != nil {
									log.Printf("textsecure.AddDevice() fail: %+v", err)
									c.sendString("X :Could not register device: " + err.Error())
								} else {
									log.Printf("Linked new device for %s", tel)
									ioutil.WriteFile(devfile, []byte(deviceURL+"\r\n"), 0666)
								}
							}
						}
					}
					err = textsecure.StartListening()
					if err != nil {
						log.Printf("Error in textsecure.StartListening(): %+v", err)
						c.sendString("X :Error in textsecure.StartListening(): " + err.Error())
						//c.tscStop(ctx) // Not thread safe.
						return
					}
					log.Printf("textsecure.StartListening() exited successfully")
				}()
			}
		}
	case "NICK":
		if c.tsc == nil {
			c.needPass(msg.Command)
		} else {
			newNick, _ := earg(msg, 0)
			oldNick := c.nick
			if newNick == "" || newNick == "*" {
				//
			} else if newNick != oldNick {
				c.setNick(newNick)
				if oldNick == "*" {
					c.sendIntro()
				} else {
					c.sendString(":" + oldNick + " NICK " + newNick)
				}
			}
		}
	case "TSLEEP":
		fstr, _ := earg(msg, 0)
		f, _ := strconv.ParseFloat(fstr, 64)
		c.tsleep = time.Duration(float64(time.Second) * f)
		c.sendString(":" + ServerName + " 300 " + c.nick + " :" + fmt.Sprintf("%v", f))
	case "USER":
		anywork = false
	case "JOIN":
		anywork = false
	case "PART":
		anywork = false
	case "BATCH":
		anywork = false
		if c.batching && c.batchMsg.Len() > 0 {
			c.tsFlushBatch()
			anywork = true
		}
		btag, _ := earg(msg, 0)
		btype, _ := earg(msg, 0)
		if btag != "" && btag[0] == '+' && btype == ServerName+"/TBATCHMSG" {
			c.batching = true
		}
	case "PRIVMSG":
		//log.Printf("-> %#v", msg)
		target, _ := earg(msg, 0)
		ircMessage, _ := eargTrailing(msg, 1)
		message := stripCodes(ircMessage)
		if target != "" && message != "" {
			if strings.EqualFold(target, c.nick) {
				// Don't send to myself.
			} else if strings.EqualFold(target, VerifyName) {
				sent := false
				if c.verifyChan != nil {
					select {
					case c.verifyChan <- message:
						sent = true
					default:
					}
				}
				if !sent {
					c.sendString(":" + VerifyName + " PRIVMSG " + c.getNick() +
						" :Not expecting a verification code")
				}
			} else {
				if c.tsc == nil {
					c.needPass(msg.Command)
				} else {
					if c.batching {
						if c.batchTarget == "" {
							c.batchTarget = target
						} else if c.batchMsg.Len() > 0 && target != c.batchTarget {
							// Auto flush batch if different target.
							c.tsFlushBatch()
						}
					}
					const actionPrefix = "\x01ACTION "
					if strings.HasPrefix(message, actionPrefix) {
						message = "* " + strings.TrimRight(message[len(actionPrefix):], "\x01")
					}
					if c.batchTarget == target {
						if c.batchMsg.Len() > 0 {
							c.batchMsg.WriteByte('\n')
						}
						c.batchMsg.WriteString(message)
						anywork = false
					} else {
						c.tsSendMsg(target, message)
					}
				}
			}
		}
	case "NOTICE":
		if c.tsc != nil {
			target, _ := earg(msg, 0)
			ircMessage, _ := eargTrailing(msg, 1)
			message := stripCodes(ircMessage)
			if target != "" && message != "" {
				c.tsSendMsg(target, "Notice: "+message)
			}
		}
	case "PING":
		arg, _ := earg(msg, 0)
		c.sendString(":" + ServerName + " PONG " + ServerName + " :" + arg)
	case "PONG":
	case "QUIT":
		arg, _ := earg(msg, 0)
		c.sendString("X :Quit: " + arg)
	case "CAP":
		// https://ircv3.net/specs/core/capability-negotiation.html
		subcmd, _ := earg(msg, 0)
		subcmd = strings.ToUpper(subcmd)
		switch subcmd {
		case "LS":
			// List supported caps.
			c.sendString("CAP " + c.nick + " ACK :" + strings.Join(capsSupported, " "))
		case "REQ":
			newCapsStr, _ := eargTrailing(msg, 1)
			newCaps := strings.Fields(newCapsStr)
			capsGood := true
			for _, newCap := range newCaps {
				if !strInStrs(newCap, capsSupported) {
					capsGood = false
					break
				}
			}
			if capsGood {
				for _, newCap := range newCaps {
					if !c.hasCapEnabled(newCap) {
						c.capsEnabled = append(c.capsEnabled, newCap)
					}
				}
				c.sendString("CAP " + c.nick + " ACK :" + newCapsStr)
			} else {
				c.sendString("CAP " + c.nick + " NAK :" + newCapsStr)
			}
		case "LIST":
			// List enabled caps.
			c.sendString("CAP " + c.nick + " ACK :" + strings.Join(c.capsEnabled, " "))
		case "END": // TODO: support.
		default:
		}
	default:
		c.sendString(":" + ServerName + " 421 " + msg.Command + " :Unknown command")
	}
	if anywork {
		time.Sleep(c.tsleep)
	}
	return c.err
}

func (c *client) sendIntro() {
	c.sendString(":" + ServerName + " 001 " + c.nick + " :Welcome to " + NetworkName)
	c.sendString((":" + ServerName + " 005 " + c.nick +
		" NETWORK=" + NetworkName + " CASEMAPPING=ascii CHANTYPES=#" +
		" NICKLEN=500 TSLEEP TBATCHMSG TSLINK :are supported by this server"))
	c.sendString(":" + ServerName + " 422 " + c.nick + " :No MOTD")
}

func getNick(tsmsg *textsecure.Message) string {
	return tsmsg.Source()
}

func getHost(tsmsg *textsecure.Message) string {
	src := tsmsg.Source()
	if strings.HasPrefix(src, "+") {
		return src[1:] + ".tel." + ServerName
	} else {
		return src + ".user." + ServerName
	}
}

func getIdent(tsmsg *textsecure.Message) string {
	sum := md5.Sum([]byte(tsmsg.SourceUUID()))
	return hex.EncodeToString(sum[:4])
}

func getFullAddress(tsmsg *textsecure.Message) string {
	return getNick(tsmsg) + "!" + getIdent(tsmsg) + "@" + getHost(tsmsg)
}

func getAccount(tsmsg *textsecure.Message) string {
	return tsmsg.SourceUUID()
}

func strInStrs(str string, strs []string) bool {
	for _, s := range strs {
		if s == str {
			return true
		}
	}
	return false
}

// https://github.com/myano/jenni/wiki/IRC-String-Formatting
var regexpCodes = regexp.MustCompile(`[\x02\x1D\x1F\x0F\x16]|\x03(\d\d?(,\d\d?)?)?`)

// stripCodes strips IRC color and other formatting codes from the string.
func stripCodes(s string) string {
	return regexpCodes.ReplaceAllLiteralString(s, "")
}

func scanNewlineTerm(data []byte, atEOF bool) (advance int, token []byte, err error) {
	if i := bytes.IndexByte(data, '\n'); i >= 0 {
		return i + 1, bytes.TrimRight(data[0:i], "\r"), nil
	}
	if atEOF { // Ignore anything at end without newline.
		return len(data), nil, nil
	}
	return 0, nil, nil // Request more data.
}

func main() {
	err := run()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %+v\n", err)
		log.Fatal(err)
	}
}
