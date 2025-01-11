package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"math"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

type Member struct {
	DNSName   string
	IP        string
	Timestamp string
	Version   int
	Port      int
}

type MembershipList struct {
	members  map[string]Member
	versions map[string]int
	incars   map[string]int
	lock     sync.RWMutex
}

type UpdateMessage struct {
	member Member
	update string
}

type IDtoDNS struct {
	ID      int
	DNSName string
}

type FileChange struct {
	Timestamp string
	Start     int
	Length    int
}

type WhereChange struct {
	whichVM    int
	fileChange FileChange
}

var membersList MembershipList
var memberRunning bool
var mergeOK bool

var rainStormStatus bool

var pattern string
var operation1 string
var operation2 string

var updatesQueue []string

var appendDict = make(map[string][]FileChange)
var cache []string
var bufferOp1 []string
var bufferOp2 []string

var myPort = 8080
var status_sus bool = false

var portMappings = make(map[string][]int)
var categoryCount = make(map[string]map[string]int)

var myIP = "172.22.156.122"
var myName = "fa24-cs425-3701.cs.illinois.edu"
var myID = 1

// var myIP = "172.22.158.122"
// var myName = "fa24-cs425-3702.cs.illinois.edu"
// var myID = 2

// var myIP = "172.22.94.122"
// var myName = "fa24-cs425-3703.cs.illinois.edu"
// var myID = 3

// var myIP = "172.22.156.123"
// var myName = "fa24-cs425-3704.cs.illinois.edu"
// var myID = 4

// var myIP = "172.22.158.123"
// var myName = "fa24-cs425-3705.cs.illinois.edu"
// var myID = 5

// var myIP = "172.22.94.123"
// var myName = "fa24-cs425-3706.cs.illinois.edu"
// var myID = 6

// var myIP = "172.22.156.124"
// var myName = "fa24-cs425-3707.cs.illinois.edu"
// var myID = 7

// var myIP = "172.22.158.124"
// var myName = "fa24-cs425-3708.cs.illinois.edu"
// var myID = 8

// var myIP = "172.22.94.124"
// var myName = "fa24-cs425-3709.cs.illinois.edu"
// var myID = 9

// var myIP = "172.22.156.125"
// var myName = "fa24-cs425-3710.cs.illinois.edu"
// var myID = 10

/**********************************************/

var introducerIP = "172.22.156.122"
var introducerPort = 8080
var introducerName = "fa24-cs425-3701.cs.illinois.edu"

var sourceVMs = []string{}
var op1VMs = []string{}
var op2VMs = []string{}
var toOp1Ports = []int{8084, 8085, 8086}
var toOp2Ports = []int{8087, 8088, 8089}

var sourceLogFiles = []string{"sourceoutput_1.log", "sourceoutput_2.log", "sourceoutput_3.log"}
var op1LogFiles = []string{"op1output_1.log", "op1output_2.log", "op1output_3.log"}
var op2LogFiles = []string{"op2output_1.log", "op2output_2.log", "op2output_3.log"}

// var cumulativeOp1LogFile = "op1output_cumulative.log"
// var cumulativeOp2LogFile = "op2output_cumulative.log"

/* The following helper functions assist operations with the Membership List */
func Remove(list *MembershipList, Name string) {
	list.lock.Lock()
	if _, exists := list.members[Name]; exists {
		delete(list.members, Name)
		go VMleft(Name)
	}
	list.lock.Unlock()
}

func Add(list *MembershipList, add_member Member) {
	if add_member.DNSName == "" || add_member.IP == "" {
		// fmt.Printf("Attempted to add invalid member: %+v\n", add_member)
		return
	}
	list.lock.Lock()
	_, exists := list.members[add_member.DNSName]
	if !exists {
		list.members[add_member.DNSName] = add_member
		go VMjoined(add_member.DNSName)
	}
	list.lock.Unlock()
}

func Get(list *MembershipList) []Member {
	list.lock.RLock()
	members := make([]Member, 0, len(list.members))
	for _, m := range list.members {
		members = append(members, m)
	}
	list.lock.RUnlock()
	return members
}

/* Remove a specific update from the Update Queue */
func removeUpdate(DNSName string) {
	newQueue := []string{}
	for _, update := range updatesQueue {
		parts := strings.Split(update, "+")
		if parts[1] != DNSName {
			newQueue = append(newQueue, update)
		}
	}
	updatesQueue = newQueue
}

/* Helper function to write to a log file starting with "machine" keyword */
func createLogs(entry string) {
	files, _ := os.ReadDir(".")
	for _, file := range files {
		if !file.IsDir() && strings.HasPrefix(file.Name(), "machine") {
			logFile, _ := os.Open(file.Name())
			scanner := bufio.NewScanner(logFile)
			entryExists := false
			for scanner.Scan() {
				if scanner.Text() == entry {
					entryExists = true
					break
				}
			}

			if !entryExists {
				logFile, _ := os.OpenFile(file.Name(), os.O_WRONLY|os.O_APPEND|os.O_CREATE, 0644)

				writer := bufio.NewWriter(logFile)
				writer.WriteString(entry)
				writer.WriteString("\n")
				writer.Flush()

				logFile.Close()
			}

			logFile.Close()
			break
		}
	}
}

/*
 * The main server function. Processes incoming ping requests, including dissemination messages, and makes
 * appropriate changes in the local membership list. Similarly parses suspicious and alive machines.
 */
func server() {
	message := make([]byte, 10000)
	udpAddress := net.UDPAddr{
		IP:   net.ParseIP(myIP),
		Port: myPort,
	}

	server, _ := net.ListenUDP("udp", &udpAddress)

	if myName == introducerName {
		memberRunning = true
	}

	for {
		if memberRunning {
			length, remoteVM, _ := server.ReadFromUDP(message)
			received := message[:length]
			senderIP := remoteVM.IP.String()

			if string(received[:4]) == "ping" && length == 4 {
				/* Simple send ack */
				ack := []byte("ack")
				server.WriteToUDP(ack, remoteVM)
			} else if string(received[:5]) == "ping+" {
				/* Need to parse dissemination message */
				parts := strings.Split(string(received[:length]), "+")

				version, _ := strconv.Atoi(parts[4])
				port, _ := strconv.Atoi(parts[5])

				newMember := Member{
					DNSName:   parts[1],
					IP:        parts[2],
					Timestamp: parts[3],
					Version:   version,
					Port:      port,
				}

				_, ok := membersList.versions[newMember.DNSName]
				_, inML := membersList.members[newMember.DNSName]

				time1, _ := time.Parse(time.RFC3339, newMember.Timestamp)
				time2, _ := time.Parse(time.RFC3339, membersList.members[newMember.DNSName].Timestamp)

				if (!ok || (newMember.Version >= membersList.versions[newMember.DNSName]) || time1.After(time2)) && memberRunning {
					/* This if statement begins conditions under which the local membership should change */
					if parts[6] == "join" && newMember.Version == 0 && ok && newMember.DNSName != myName && !inML {
						/* Edge case join condition where you join after crashing; introducer must recognize and fix the version number */
						newMember.Version = membersList.versions[newMember.DNSName] + 1
						membersList.versions[newMember.DNSName]++
						received = []byte(fmt.Sprintf("ping+%s+%s+%s+%d+%d+join", newMember.DNSName, newMember.IP, newMember.Timestamp, newMember.Version, newMember.Port))
						Add(&membersList, newMember)
						createLogs(string(received))
					} else if parts[6] == "sus" && (time1.After(time2)) {
						/* Parse a suspicious machine message */
						incar, _ := strconv.Atoi(parts[7])
						if newMember.DNSName == myName {
							member := membersList.members[newMember.DNSName]
							member.Timestamp = time.Now().Format(time.RFC3339)
							membersList.members[newMember.DNSName] = member

							membersList.incars[myName]++
							aliveString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+alive+%d", newMember.DNSName, newMember.IP, string(time.Now().Format(time.RFC3339)), newMember.Version, newMember.Port, membersList.incars[newMember.DNSName])
							removeUpdate(newMember.DNSName)
							updatesQueue = append(updatesQueue, string(aliveString))
						} else if incar > membersList.incars[newMember.DNSName] {
							membersList.incars[newMember.DNSName] = incar
							removeUpdate(newMember.DNSName)
							updatesQueue = append(updatesQueue, string(received))
						}
						continue
					} else if parts[6] == "alive" && (time1.After(time2)) {
						incar, _ := strconv.Atoi(parts[7])
						if incar > membersList.incars[newMember.DNSName] {
							for _, update := range updatesQueue {
								parts := strings.Split(update, "+")
								if parts[1] == newMember.DNSName {
									if parts[6] == "sus" {
										member := membersList.members[newMember.DNSName]
										member.Timestamp = time.Now().Format(time.RFC3339)
										membersList.members[newMember.DNSName] = member

										membersList.incars[newMember.DNSName] = incar
										removeUpdate(newMember.DNSName)
										updatesQueue = append(updatesQueue, string(received))
									}
									break
								}
							}
						}
						/* Skip rest of the loop if we recognized an alive node */
						continue
					}

					removeUpdate(newMember.DNSName)
					updatesQueue = append(updatesQueue, string(received))

					if (parts[6] == "join" && (newMember.Version > membersList.versions[newMember.DNSName])) || !ok {
						membersList.versions[newMember.DNSName] = newMember.Version
						Add(&membersList, newMember)
						createLogs(string(received))
					} else if parts[6] == "leave" && (time1.After(time2)) {
						Remove(&membersList, newMember.DNSName)
						createLogs(string(senderIP) + " notified that " + parts[1] + " failed.")
						createLogs(string(received))
					}
				} else {
					/* Condition where we only need to disseminate without local updates */
					existingVersion := -1
					for _, update := range updatesQueue {
						parts := strings.Split(update, "+")
						if parts[1] == newMember.DNSName {
							existingVersion, _ = strconv.Atoi(parts[4])
							break
						}
					}

					if existingVersion == -1 || newMember.Version >= existingVersion {
						removeUpdate(newMember.DNSName)
						updatesQueue = append(updatesQueue, string(received))
					}
				}

				ack := []byte("ack")
				server.WriteToUDP(ack, remoteVM)
			}
		} else {
			/* To avoid receiving requests, if we are not running (if we have left) close the server and wait */
			server.Close()
			for !memberRunning {
				time.Sleep(50 * time.Millisecond)
			}
			server, _ = net.ListenUDP("udp", &udpAddress)
		}
	}
	server.Close()
}

/*
 * The main client function. Periodically ping random nodes and check for ack. Will also add messages
 * to disseminate from the local queue so that the latest messages are propogated.
 */
func client(IP string, Port int, DNSName string) {
	client, _ := net.Dial("udp", IP+":"+strconv.Itoa(Port))

	message := "nil"

	if len(updatesQueue) != 0 {
		/* Rotate the queue after picking the first value */
		message = updatesQueue[0]
		for len(message) >= 6 && message[:6] == "ping++" {
			updatesQueue = updatesQueue[1:]
			message = updatesQueue[0]
		}
		updatesQueue = append(updatesQueue[1:], updatesQueue[0])
	}

	if message != "nil" {
		fmt.Fprintf(client, message)
	} else {
		fmt.Fprintf(client, "ping")
	}

	response := make([]byte, 10000)

	_, err := bufio.NewReader(client).Read(response)

	if err == nil {
		/* Expected response with ack or other message */
		if string(response[:3]) == "ack" {
		} else {
			fmt.Printf("Did not receive ack, instead got: " + string(response))
		}
	} else {
		/* If we do not receive a response, investigate by trying with a timeout */
		client.SetReadDeadline(time.Now().Add(6 * time.Second))

		/* Wait for timeout to make sure it's dead */

		_, err := bufio.NewReader(client).Read(response)
		if err == nil {
			if string(response[:3]) == "ack" {
			} else {
				Remove(&membersList, DNSName)
				fmt.Printf("Did not receive ack, instead got: " + string(response))
			}
		} else if netErr, ok := err.(net.Error); ok && netErr.Timeout() && DNSName != "" && DNSName != myName {
			fmt.Println("Ping timed out for " + DNSName)

			failed := membersList.members[DNSName]
			failedString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+leave", failed.DNSName, failed.IP, string(time.Now().Format(time.RFC3339)), failed.Version, failed.Port)
			removeUpdate(failed.DNSName)
			updatesQueue = append(updatesQueue, string(failedString))
			Remove(&membersList, DNSName)
			membersList.versions[DNSName] = failed.Version
		} else if DNSName != "" && DNSName != myName {
			failed := membersList.members[DNSName]
			failedString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+leave", failed.DNSName, failed.IP, string(time.Now().Format(time.RFC3339)), failed.Version, failed.Port)
			removeUpdate(failed.DNSName)
			updatesQueue = append(updatesQueue, string(failedString))
			Remove(&membersList, DNSName)
			membersList.versions[DNSName] = failed.Version
			fmt.Printf("Timeout: ")
			fmt.Printf("%v", err)
		}
	}
	client.Close()
}

func susClient(IP string, Port int, DNSName string) {
	client, _ := net.Dial("udp", IP+":"+strconv.Itoa(Port))

	message := "nil"

	if len(updatesQueue) != 0 {
		message = updatesQueue[0]
		updatesQueue = append(updatesQueue[1:], updatesQueue[0])
	}

	if message != "nil" {
		fmt.Fprintf(client, message)
	} else {
		fmt.Fprintf(client, "ping")
	}

	response := make([]byte, 10000)

	_, err := bufio.NewReader(client).Read(response)

	if err == nil {
		if string(response[:3]) == "ack" {
			for _, update := range updatesQueue {
				parts := strings.Split(update, "+")
				if parts[1] == DNSName {
					if parts[6] == "sus" {
						member := membersList.members[DNSName]
						member.Timestamp = time.Now().Format(time.RFC3339)
						membersList.members[DNSName] = member

						aliveString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+alive+%d", parts[1], parts[2], string(time.Now().Format(time.RFC3339)), parts[4], parts[5], parts[7])
						removeUpdate(DNSName)
						updatesQueue = append(updatesQueue, string(aliveString))
					}
					break
				}
			}
		} else {
			fmt.Printf("Did not receive ack, instead got: " + string(response))
		}
	} else {

		client.SetReadDeadline(time.Now().Add(6 * time.Second))

		/* Wait for timeout to make sure it's dead */

		_, err := bufio.NewReader(client).Read(response)
		if err == nil {
			if string(response[:3]) == "ack" {
			} else {
				fmt.Printf("Did not receive ack, instead got: " + string(response))
			}
		} else if netErr, ok := err.(net.Error); ok && netErr.Timeout() && DNSName != myName {
			fmt.Println("Ping timed out for " + DNSName)

			failed := membersList.members[DNSName]
			failedString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+sus+%d", failed.DNSName, failed.IP, string(time.Now().Format(time.RFC3339)), failed.Version, failed.Port, membersList.incars[failed.DNSName])
			removeUpdate(failed.DNSName)
			updatesQueue = append(updatesQueue, string(failedString))
			membersList.versions[DNSName] = failed.Version
			/* Wait to see if suspicious node clarifies itself as alive */
			fmt.Println("Marked node " + failed.DNSName + " as suspicious.")
			go markSus(failed)

		} else {
			failed := membersList.members[DNSName]
			failedString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+leave", failed.DNSName, failed.IP, string(time.Now().Format(time.RFC3339)), failed.Version, failed.Port)
			removeUpdate(failed.DNSName)
			updatesQueue = append(updatesQueue, string(failedString))
			Remove(&membersList, DNSName)
			membersList.versions[DNSName] = failed.Version
			fmt.Printf("Timeout: ")
			fmt.Printf("%v", err)
		}
	}
	client.Close()
}

/* This function marks a process as sus and if it doesnt receive any alive message
 * within a time frame, it removed it from the memberhsip list and propagates the message
 */
func markSus(sus Member) {
	time.Sleep(8 * time.Second)

	for _, update := range updatesQueue {
		parts := strings.Split(update, "+")
		if parts[1] == sus.DNSName {
			if parts[6] == "sus" {
				failedString := fmt.Sprintf("ping+%s+%s+%s+%d+%d+leave", sus.DNSName, sus.IP, string(time.Now().Format(time.RFC3339)), sus.Version, sus.Port)
				removeUpdate(sus.DNSName)
				updatesQueue = append(updatesQueue, string(failedString))
				Remove(&membersList, sus.DNSName)
				membersList.versions[sus.DNSName] = sus.Version
				fmt.Println("Marked suspicious node " + sus.DNSName + " as failed.")
			}
			break
		}
	}
}

/*
 * This is a simple hash function to determine PeerId. Uses sha256 hash.
 */
func dabZeeHash(filename string) string {
	hash := sha256.Sum256([]byte(filename))
	return fmt.Sprintf("%x", hash)
}

/*
 * This function uses the hash function to find a node ID corresponding to a file.
 * The  hash alone will be a hexadecimal string, which we cut and divide to get
 * a high precision float number between 0 and 10. We then round up to get our
 * expected node ID this file should be on.
 */
func getMachineID(filename string) (int, float64) {
	hashBytes := dabZeeHash(filename)
	truncated_hash := hashBytes[len(hashBytes)-15:]

	intValue, _ := strconv.ParseInt(truncated_hash, 16, 64)
	floatValue := float64(intValue)

	power := math.Floor(math.Log10(floatValue))
	floatValue = floatValue / (math.Pow10(int(power)))
	// fmt.Printf("Decimal Hash Value for %s: %.30f\n", filename, floatValue)

	machineID := int(math.Ceil(floatValue))
	// fmt.Println("Machine ID:", machineID)
	return machineID, floatValue
}

var dns_name_regex = regexp.MustCompile(`fa24-cs425-37(\d{2})\.cs\.illinois\.edu`)

type byIDNum []IDtoDNS

func (m byIDNum) Len() int           { return len(m) }
func (m byIDNum) Less(i, j int) bool { return m[i].ID < m[j].ID }
func (m byIDNum) Swap(i, j int)      { m[i], m[j] = m[j], m[i] }

/*
 * This function builds on top of getMachineID to actually find which node a file must
 * be stored on. Though the previous function identifies which node a file should be
 * stored on, this is not always possible due to failures and some VMs not being active.
 * As a result we search for the next available VM in the rign structure past the "correct" node.
 */

func getRealID(startID int) (int, string) {
	membersList.lock.RLock()
	activeNodes := []IDtoDNS{}

	// accumulate all active nodes
	for _, member := range membersList.members {
		matches := dns_name_regex.FindStringSubmatch(member.DNSName)
		if len(matches) == 2 {
			id, _ := strconv.Atoi(matches[1])
			pair := IDtoDNS{ID: id, DNSName: member.DNSName}
			activeNodes = append(activeNodes, pair)
		}
	}

	if len(activeNodes) == 0 {
		membersList.lock.RUnlock()
		return -1, "No active members"
	}

	// sort activeNodes to get the correct ring structure
	sort.Sort(byIDNum(activeNodes))

	for _, node := range activeNodes {
		if node.ID >= startID {
			membersList.lock.RUnlock()
			return node.ID, node.DNSName
		}
	}

	membersList.lock.RUnlock()
	return activeNodes[0].ID, activeNodes[0].DNSName
}

/*
 * Helper function toprint files in the DFS sttored locally.
 */
func storeFile() {
	_, err := os.Stat("DFS")
	if !os.IsNotExist(err) {
		files, _ := ioutil.ReadDir("./DFS")

		temp := fmt.Sprintf("VM %s with ID %s has the following files:", myName, strconv.Itoa(myID))
		fmt.Println(temp)

		count := 0
		for _, file := range files {
			if !file.IsDir() {
				count += 1
				_, hashVal := getMachineID(file.Name())
				temp1 := fmt.Sprintf("%d. %s %s", count, file.Name(), strconv.FormatFloat(hashVal, 'f', -1, 64))
				fmt.Println(temp1)
			}
		}
	}
}

/*
 * This function is primarily for debugging purposes. It reads and outputs
 * all DFS files stored at all nodes.
 */
func storeFileAll() {
	fmt.Println("Listing all VM addresses, VM ID's, and files at each VM...")

	allMembers := Get(&membersList)
	for _, member := range allMembers {
		client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
		// send request to each server to grab all files
		fmt.Fprintf(client, "needAllFiles")
		original := make([]byte, 10000)
		length, err := bufio.NewReader(client).Read(original)
		response := original[:length]
		if err == nil {
			if string(response[:13]) == "hereAllFiles+" {
				fileNames := string(response[13:])
				listFiles := strings.Split(fileNames, "+")
				matches := dns_name_regex.FindStringSubmatch(member.DNSName)
				temp := fmt.Sprintf("VM %s with ID %s has the following files:", member.DNSName, matches[1])
				fmt.Println(temp)
				count := 0
				for _, file := range listFiles {
					count += 1
					_, hashVal := getMachineID(file)
					temp1 := fmt.Sprintf("%d. %s %s", count, file, strconv.FormatFloat(hashVal, 'f', -1, 64))
					fmt.Println(temp1)
				}
				fmt.Println("*********************************************************************")
			}
		}
		client.Close()
	}

}

type orderDNS []Member

func (x orderDNS) Len() int           { return len(x) }
func (x orderDNS) Swap(i, j int)      { x[i], x[j] = x[j], x[i] }
func (x orderDNS) Less(i, j int) bool { return x[i].DNSName < x[j].DNSName }

/*
 * List all members of the membership list along with their node IDs.
 */
func listMemIds() {
	allMembers := Get(&membersList)
	sort.Sort(orderDNS(allMembers))
	fmt.Println("            DNS Name             |   IP Address   |         Timestamp         | Version | Port | RingId ")
	fmt.Println("--------------------------------------------------------------------------------------------------------")

	for _, member := range allMembers {
		matches := dns_name_regex.FindStringSubmatch(member.DNSName)
		id, _ := strconv.Atoi(matches[1])
		entry := fmt.Sprintf(" %s | %s | %s |    %d    | %d | %d", member.DNSName, member.IP, member.Timestamp, member.Version, member.Port, id)
		fmt.Println(entry)
	}

	return
}

type orderTimes []FileChange

func (a orderTimes) Len() int      { return len(a) }
func (a orderTimes) Swap(i, j int) { a[i], a[j] = a[j], a[i] }
func (a orderTimes) Less(i, j int) bool {
	time1, _ := time.Parse(time.RFC3339, a[i].Timestamp)
	time2, _ := time.Parse(time.RFC3339, a[j].Timestamp)
	return time1.Before(time2)
}

/*
 * This function reads append blocks to a certain file, rearranges them in
 * the order they were received, and writes them to all replicas to ensure
 * consistency. The algorithm used basically pulls changes one at a time
 * and compares.
 */
func merge(dfsfileName string) {
	startTime := time.Now()
	// check if dfsfilename is in the DFS directory of the VM
	localFilePath := fmt.Sprintf("./DFS/%s", dfsfileName)
	_, err := os.Stat(localFilePath)
	calcID, _ := getMachineID(dfsfileName)
	actualID, _ := getRealID(calcID)
	if actualID == myID && !os.IsNotExist(err) {

		// It is fine to do this in client because we can assume no concurent updates/failures
		// if it is:
		// retrive the local append dict.
		localChanges := appendDict[dfsfileName] // type []FileChange
		sort.Sort(orderTimes(localChanges))

		// Also get append dict and actual replica files from replicas to make sure no extra data in those
		secondID, VMAddress2 := getRealID(myID + 1)
		secondChanges := getChanges(VMAddress2, dfsfileName)
		sort.Sort(orderTimes(secondChanges))

		thirdID, VMAddress3 := getRealID(secondID + 1)
		thirdChanges := getChanges(VMAddress3, dfsfileName)
		sort.Sort(orderTimes(thirdChanges))

		// If mergeOK everywhere (meaning merge just happened no changes) then return
		// if mergeOK && status2 && status3 { return }

		// Get full replica files in case they have additional data
		getFileR(myName, dfsfileName, "_first_copy_.txt")
		defer os.Remove("_first_copy_.txt")
		getFileR(VMAddress2, dfsfileName, "_second_copy_.txt")
		defer os.Remove("_second_copy_.txt")
		getFileR(VMAddress3, dfsfileName, "_third_copy_.txt")
		defer os.Remove("_third_copy_.txt")

		var allChanges []WhereChange
		// maxLen := math.Max(float64(len(localChanges)), math.Max(float64(len(secondChanges)), float64(len(thirdChanges))))
		for len(localChanges) > 0 || len(secondChanges) > 0 || len(thirdChanges) > 0 {
			if localChanges[0] == secondChanges[0] && secondChanges[0] == thirdChanges[0] {
				newVal := WhereChange{whichVM: 1, fileChange: localChanges[0]}
				allChanges = append(allChanges, newVal)
				localChanges = localChanges[1:]
				secondChanges = secondChanges[1:]
				thirdChanges = thirdChanges[1:]
			} else if isTimeLeast(localChanges[0], secondChanges[0], thirdChanges[0]) {
				newVal := WhereChange{whichVM: 1, fileChange: localChanges[0]}
				allChanges = append(allChanges, newVal)
				localChanges = localChanges[1:]
			} else if isTimeLeast(secondChanges[0], localChanges[0], thirdChanges[0]) {
				newVal := WhereChange{whichVM: 2, fileChange: secondChanges[0]}
				allChanges = append(allChanges, newVal)
				localChanges = secondChanges[1:]
			} else if isTimeLeast(thirdChanges[0], secondChanges[0], localChanges[0]) {
				newVal := WhereChange{whichVM: 3, fileChange: thirdChanges[0]}
				allChanges = append(allChanges, newVal)
				localChanges = thirdChanges[1:]
			} else if localChanges[0] == secondChanges[0] {
				newVal := WhereChange{whichVM: 1, fileChange: localChanges[0]}
				allChanges = append(allChanges, newVal)
				localChanges = localChanges[1:]
				secondChanges = secondChanges[1:]
			} else if localChanges[0] == thirdChanges[0] {
				newVal := WhereChange{whichVM: 1, fileChange: localChanges[0]}
				allChanges = append(allChanges, newVal)
				localChanges = localChanges[1:]
				thirdChanges = thirdChanges[1:]
			} else if thirdChanges[0] == secondChanges[0] {
				newVal := WhereChange{whichVM: 3, fileChange: thirdChanges[0]}
				allChanges = append(allChanges, newVal)
				thirdChanges = thirdChanges[1:]
				secondChanges = secondChanges[1:]
			}
		}

		// create a temporary new file
		mergedFile, _ := os.Create("_Temp_Merged_.txt")
		defer os.Remove("_Temp_Merged_.txt")

		firstFile, _ := os.Open("_first_copy_.txt")
		defer firstFile.Close()
		secondFile, _ := os.Open("_second_copy_.txt")
		defer secondFile.Close()
		thirdFile, _ := os.Open("_third_copy_.txt")
		defer thirdFile.Close()

		currentPos := 0
		for _, change := range allChanges {
			var sourceFile *os.File
			switch change.whichVM {
			case 1:
				sourceFile = firstFile
			case 2:
				sourceFile = secondFile
			case 3:
				sourceFile = thirdFile
			}

			sourceFile.Seek(int64(change.fileChange.Start), io.SeekStart)

			buffer := make([]byte, change.fileChange.Length)
			_, _ = sourceFile.Read(buffer)

			fmt.Println(string(buffer))

			_, _ = mergedFile.Write(buffer)

			currentPos += change.fileChange.Length
		}

		// update local appendDict
		appendDict[dfsfileName] = make([]FileChange, len(allChanges))
		for i, change := range allChanges {
			appendDict[dfsfileName][i] = change.fileChange
		}

		// overwrite DFS file with the newly constructed copy
		sourceFile := "_Temp_Merged_.txt"

		dest, _ := os.Open(localFilePath) // This will overwrite the destination file if it exists
		defer dest.Close()

		io.Copy(dest, mergedFile)

		// write to the replica files.

		secondVMAddress := ""
		thirdVMAddress := ""

		if secondID != 10 {
			secondVMAddress = fmt.Sprintf("fa24-cs425-370" + strconv.Itoa(secondID) + ".cs.illinois.edu")
		} else {
			secondVMAddress = fmt.Sprintf("fa24-cs425-37" + strconv.Itoa(secondID) + ".cs.illinois.edu")
		}

		if thirdID != 10 {
			thirdVMAddress = fmt.Sprintf("fa24-cs425-370" + strconv.Itoa(thirdID) + ".cs.illinois.edu")
		} else {
			thirdVMAddress = fmt.Sprintf("fa24-cs425-37" + strconv.Itoa(thirdID) + ".cs.illinois.edu")
		}

		content, _ := os.ReadFile(sourceFile)

		// fmt.Println("CONTENT: " + string(content))

		allMembers := Get(&membersList)
		for _, member := range allMembers {
			if member.DNSName == secondVMAddress {
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
				appendInfo := fmt.Sprintf("repmerge+%s+%s", dfsfileName, content)
				fmt.Fprintf(client, appendInfo)
			}
		}
		for _, member := range allMembers {
			if member.DNSName == thirdVMAddress {
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
				appendInfo := fmt.Sprintf("repmerge+%s+%s", dfsfileName, content)
				fmt.Fprintf(client, appendInfo)
			}
		}

		fmt.Println("Successfully completed merge")

	} else {
		peerId, _ := getMachineID(dfsfileName)
		_, dns := getRealID(peerId)
		allMembers := Get(&membersList)
		for _, member := range allMembers {
			if member.DNSName == dns {
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
				mergeInfo := fmt.Sprintf("mergeFile+%s", dfsfileName)
				fmt.Fprintf(client, mergeInfo)
			}
		}
	}
	endTime := time.Now()
	diff := endTime.Sub(startTime)
	fmt.Println("Time difference: ", diff)
}

/* retrieves the appendDict data structure for the replicas of a certain file*/
func getChanges(VMAddress string, dfsfileName string) []FileChange {
	var changesArr []FileChange

	allMembers := Get(&membersList)
	for _, member := range allMembers {
		if member.DNSName == VMAddress {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
			changeInfo := fmt.Sprintf("changeHAND+%s", dfsfileName)
			fmt.Fprintf(client, changeInfo)
			original := make([]byte, 10000)
			length, err := bufio.NewReader(client).Read(original)
			response := original[:length]

			/* converts the data structure to a string format via payload */
			if err == nil {
				if string(response[:6]) == "penny+" {
					payload := response[6 : len(response)-1]
					eachChanges := strings.Split(string(payload), "+")
					for _, change := range eachChanges {
						elements := strings.Split(change, "~")
						// if len(elements) == 0 { continue }
						newStart, _ := strconv.Atoi(elements[1])
						newLength, _ := strconv.Atoi(elements[2])
						currentChange := FileChange{
							Timestamp: elements[0],
							Start:     newStart,
							Length:    newLength,
						}
						changesArr = append(changesArr, currentChange)
					}
					regMessage := fmt.Sprintf("Successfully received %s's changeArray array", dfsfileName)
					fmt.Println(regMessage)
				} else {
					errorMessage := fmt.Sprintf("Error getting %s's changeArray", dfsfileName)
					fmt.Println(errorMessage)
				}
			} else {
				errorMessage := fmt.Sprintf("Error getting %s's changeArray", dfsfileName)
				fmt.Println(errorMessage)
			}

			client.Close()
		}
	}

	return changesArr

}

/* helper function to sort timestamps for merge */
func isTimeLeast(a FileChange, b FileChange, c FileChange) bool {
	time_a, _ := time.Parse(time.RFC3339, a.Timestamp)
	time_b, _ := time.Parse(time.RFC3339, b.Timestamp)
	time_c, _ := time.Parse(time.RFC3339, c.Timestamp)

	if time_a.Before(time_b) && time_a.Before(time_c) {
		return true
	}

	return false
}

/* helps to determine which VMs a certain file belongs to */
func lsFile(dfsfileName string) {
	fmt.Println("Listing all VM addresses and VM ID's...")
	fmt.Println("           VM Address           | VM ID")
	fmt.Println("--------------------------------|------")

	allMembers := Get(&membersList)
	for _, member := range allMembers {
		client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
		defer client.Close()
		fmt.Fprintf(client, "needAllFiles")
		original := make([]byte, 10000)
		length, err := bufio.NewReader(client).Read(original)
		response := original[:length]
		if err == nil {
			if string(response[:13]) == "hereAllFiles+" {
				fileNames := string(response[13:])

				/* checks to see if this file name eists for this particular machine */
				listFiles := strings.Split(fileNames, "+")
				for _, file := range listFiles {
					if file == dfsfileName {
						matches := dns_name_regex.FindStringSubmatch(member.DNSName)
						/* we break so we can save tim*/
						entry := fmt.Sprintf("%s | %s", member.DNSName, matches[1])
						fmt.Println(entry)
						break
					}
				}
			} else {
				fmt.Println("Failed LS")
				return
			}
		} else {
			fmt.Println("Failed LS")
			return
		}
	}

}

/* retrives all of the files from all of the VMs */
func getAllFiles() []string {
	var allFiles = []string{}
	allMembers := Get(&membersList)
	for _, member := range allMembers {
		client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
		// Send request to all servers
		fmt.Fprintf(client, "needAllFiles")
		original := make([]byte, 10000)
		length, err := bufio.NewReader(client).Read(original)
		response := original[:length]
		if err == nil {
			if string(response[:13]) == "hereAllFiles+" {
				fileNames := string(response[13:])
				listFiles := strings.Split(fileNames, "+")
				for _, file := range listFiles {
					allFiles = append(allFiles, file)
				}
			}
		}
		client.Close()
	}

	return allFiles

}

/* calls each VM to append the file to the DFS file */
func multiHelper(dfsfileName string, localfileName string, VMAddress string) {
	allMembers := Get(&membersList)
	for _, member := range allMembers {
		if member.DNSName == VMAddress {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
			// send request to servers contianing file
			appendInfo := fmt.Sprintf("multiappend+%s+%s", dfsfileName, localfileName)
			fmt.Fprintf(client, appendInfo)
			original := make([]byte, 64)
			/* error checking */
			length, err := bufio.NewReader(client).Read(original)
			response := original[:length]
			if err == nil {
				if string(response[:12]) == "appendworked" {
					regMessage := fmt.Sprintf("%s was successfully appended to %s", localfileName, dfsfileName)
					fmt.Println(regMessage)
				} else {
					errorMessage := fmt.Sprintf("Error appending %s to %s", localfileName, dfsfileName)
					fmt.Println(errorMessage)
					return
				}
			} else {
				errorMessage := fmt.Sprintf("Error appending %s to %s", localfileName, dfsfileName)
				fmt.Println(errorMessage)
				return
			}

			client.Close()
		}
	}
}

/*
 * This function calls multiHelper to concurrently begin append tasks from
 * different VMs.
 */
func multiAppend(dfsfileName string, vmArr []string, lfArr []string) {

	for index, _ := range lfArr {
		multiHelper(dfsfileName, lfArr[index], vmArr[index])
	}
}

/*
 * This function appends a local file to a DFS file and its replicas.
 * As a result it must calculate the replicas as well before appending to all.
 */
func appendAllFiles(localfileName string, dfsfileName string) {

	handleCacheWrite(cache, dfsfileName)

	// Find "owner" of file
	peerId, _ := getMachineID(dfsfileName)
	realid, dns := getRealID(peerId)
	file, _ := os.Open(localfileName)
	content, err := io.ReadAll(file)
	if err != nil {
		fmt.Println("Error reading local file:", err)
		return
	}
	file.Close()

	tempid := -1
	names := make([]string, 3)
	names[0] = dns
	// Calculations for next id
	tempid, names[1] = getRealID((realid % 10) + 1)
	_, names[2] = getRealID((tempid % 10) + 1)

	count := 1
	for _, name := range names {
		// Append to "owner" of file and replicas
		rv := appendFile(dfsfileName, content, name, count)
		if !rv {
			break
		}
		count++
	}

	/* validation statements */
	completed := fmt.Sprintf("Sucessfully appended %s to %s", localfileName, dfsfileName)
	fmt.Println(completed)

	replicas := fmt.Sprintf("This append was replicated on the following VMS: %s, %s", names[1], names[2])
	fmt.Println(replicas)

}

/*
 * Append a byte array to a file. If we are the owner, conduct the operation. Else,
 * send command to the server of the node who should conduct the operation.
 */
func appendFile(dfsfileName string, content []byte, dns string, count int) bool {
	if dns == myName {

		filePath := fmt.Sprintf("./DFS/%s", dfsfileName)
		_, err := os.Stat(filePath)
		if os.IsNotExist(err) {
			fmt.Println("DFS file does not exist, cannot append")
			return false
		}

		dfsFile, err := os.OpenFile(filePath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
		if err != nil {
			fmt.Println("Error opening file to append")
			return false
		}

		info, err := os.Stat(filePath)
		startSize := 0
		if err == nil {
			startSize = int(info.Size())
		}

		_, err = dfsFile.WriteString(string(content))
		if err != nil {
			fmt.Println("Error appending to file")
			return false
		}

		dfsFile.Close()

		/* add the current change to the append dictionary to be later used for merge r*/
		appendDict[dfsfileName] = append(appendDict[dfsfileName], FileChange{Timestamp: string(time.Now().Format(time.RFC3339)), Start: int(startSize), Length: len(content)})
		return true

	} else {
		// if count == 1 {
		// 	allFiles := getAllFiles()
		// 	if !slices.Contains(allFiles, dfsfileName) {
		// 		fmt.Println("DFS file does not exist, cannot append")
		// 		return false
		// 	}
		// }
		for _, member := range membersList.members {
			if member.DNSName == dns {
				// Send append to request to relavant server
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
				payload := fmt.Sprintf("appendFile+%s+%s", dfsfileName, content)
				fmt.Fprintf(client, payload)
				client.Close()
				break
			}
		}
		return true
	}
}

/* once a file is cretaed, we need to create it on the next two available machines */
func createAllFiles(localfileName string, dfsfileName string) {
	peerId, _ := getMachineID(dfsfileName)
	realid, dns := getRealID(peerId)
	file, _ := os.Open(localfileName)
	content, err := io.ReadAll(file)
	if err != nil {
		fmt.Println("Error reading local file:", err)
		return
	}
	file.Close()

	tempid := -1
	names := make([]string, 3)
	names[0] = dns
	// Calculate actual ID
	tempid, names[1] = getRealID((realid % 10) + 1)
	_, names[2] = getRealID((tempid % 10) + 1)

	count := 1
	for _, name := range names {
		rv := createFile(dfsfileName, content, name, count)
		if !rv {
			break
		}
		count++
	}

	/* validation statements */
	completed := fmt.Sprintf("Sucessfully created %s from %s", dfsfileName, localfileName)
	fmt.Println(completed)

	replicas := fmt.Sprintf("This file was replicated on the following VMS: %s, %s", names[1], names[2])
	fmt.Println(replicas)

}

/*
 * This function actually creates a file in the DFS for the first time, and fills it
* with the input byte array.
*/
func createFile(dfsfileName string, content []byte, dns string, count int) bool {

	/* edge cases taken into cosnideration when creating a file */
	if dns == myName {
		_, err := os.Stat("DFS")
		if os.IsNotExist(err) {
			err := os.Mkdir("DFS", 0755)
			if err != nil {
				fmt.Println("Failed to create DFS directory")
				return false
			}
		}

		filePath := fmt.Sprintf("./DFS/%s", dfsfileName)
		_, err = os.Stat(filePath)
		if !os.IsNotExist(err) {
			fmt.Println("DFS file already exists, can't overwrite")
			return false
		}

		info, err := os.Stat(filePath)
		startSize := 0
		if err == nil {
			startSize = int(info.Size())
		}

		err = os.WriteFile(filePath, []byte(content), 0644)
		if err != nil {
			fmt.Println("Error writing to DFS file locally: " + filePath)
		}

		/* store the first write change to our append dictionary  */
		appendDict[dfsfileName] = append(appendDict[dfsfileName], FileChange{Timestamp: string(time.Now().Format(time.RFC3339)), Start: int(startSize), Length: len(content)})

	} else {
		/* ask the VM who would store the primary replica to create the file*/

		for _, member := range membersList.members {
			if member.DNSName == dns {
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
				payload := "writeFile+" + dfsfileName + "+" + string(content)
				fmt.Fprintf(client, payload)
				client.Close()
				break
			}
		}
	}

	return true
}

/* ensures that the cache is reflective of the writes */
func handleCacheWrite(arr []string, dfsfileName string) []string {
	result := []string{}
	var dfsFileExists bool = false

	for _, elem := range arr {
		if elem != dfsfileName {
			result = append(result, elem)
		} else if elem == dfsfileName {
			dfsFileExists = true
		}
	}

	/* removes a file in the cache if it has been written */
	if dfsFileExists {
		filePath := fmt.Sprintf("./cache/", dfsfileName)
		err := os.Remove(filePath)
		if err != nil {
			fmt.Println("Error deleting file:", err)
			return result
		}
	}

	return result
}

/*
 * This function gets the indicated file to a local copy.
 */
func getFile(dfsfileName string, localfileName string) {
	content := ""

	/* Check to see if file exists in cache, if it does read it  */
	var dfsFileExists bool = false
	if slices.Contains(cache, dfsfileName) {
		dfsFileExists = true
		filePath := fmt.Sprintf("./cache/", dfsfileName)
		file, _ := os.Open(filePath)
		temp, _ := io.ReadAll(file)
		content = string(temp)
		file.Close()
	}

	/* if the file is not in the cache, then we actually have to retrieve it*/
	if dfsFileExists == false {
		peerId, _ := getMachineID(dfsfileName)
		_, dns := getRealID(peerId)
		allFiles := getAllFiles()

		if !slices.Contains(allFiles, dfsfileName) {
			fmt.Println("DFS file does not exist.")
			return
		} else {
			for _, member := range membersList.members {
				if member.DNSName == dns {
					client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
					payload := fmt.Sprintf("needFile+%s", dfsfileName)
					fmt.Fprintf(client, payload)

					original := make([]byte, 10000)
					length, err := bufio.NewReader(client).Read(original)
					if err == nil {
						response := original[:length]
						if string(response[:9]) == "hereFile+" {
							somethingElse := string(response[9:])
							thing := strings.Split(somethingElse, "+")
							if thing[0] != dfsfileName {
								fmt.Println("This is not the correct content of file")
								return
							} else {
								content = thing[1]
							}
						}

						/* add to cache if file does not exist for future get requests */
						_, err := os.Stat("cache")
						if os.IsNotExist(err) {
							err := os.Mkdir("cache", 0755)
							if err != nil {
								fmt.Println("Failed to create Cache directory")
								return
							}
						}

						if len(cache) < 6 {
							cache = append(cache, dfsfileName)
						} else {
							filePath := fmt.Sprintf("./cache/", cache[0])
							err := os.Remove(filePath)
							if err != nil {
								fmt.Println("Error deleting file:", err)
								return
							}

							cache = append(cache[1:], dfsfileName)

						}
						filePath := fmt.Sprintf("./cache/", dfsfileName)
						err = os.WriteFile(filePath, []byte(content), 0644)
						if err != nil {
							fmt.Println("Error writing to cache")
							return
						}

					}
					client.Close()
					break
				}
			}
		}
	}

	filePath := fmt.Sprintf("./%s", localfileName)

	/* WriteFile creates a file if it doesn't exist, and always overwrites existing file */
	err := os.WriteFile(filePath, []byte(content), 0644)
	if err != nil {
		fmt.Println("Error writing to local file")
		return
	}

	completed := fmt.Sprintf("Sucessfully placed %s into %s", dfsfileName, localfileName)
	fmt.Println(completed)
}

func replaceTask(replacement string, taskType string, version int) {
	for _, member := range membersList.members {
		if member.DNSName == replacement {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8082))
			message := fmt.Sprintf("replaceTask+%s+%d", taskType, version)
			fmt.Fprintf(client, message)
			break
		}
	}
}

func deleteTask(secondaryVM string, taskType string, version int, VMport int) {
	for _, member := range membersList.members {
		if member.DNSName == secondaryVM {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8082))
			message := fmt.Sprintf("deleteTask+%s+%d", taskType, version)
			fmt.Fprintf(client, message)

			original := make([]byte, 10000)
			length, err := bufio.NewReader(client).Read(original)
			if err == nil {
				response := original[:length]
				if string(response[:15]) == "startedProcess+" {
					result := []int{}
					for _, val := range portMappings[secondaryVM] {
						if val != VMport {
							result = append(result, val)
						}
					}

					portMappings[secondaryVM] = result
				}
			}

			break
		}
	}
}

func resendMissing(inputFile string, checkFile string, newVM string, index int, operation string) {
	inputLastLine := getLastLineNumber(inputFile)
	outputLastLine := getLastLineNumber(checkFile)

	if inputLastLine > outputLastLine {
		file, _ := os.Open(inputFile)
		defer file.Close()

		var missingLines []string
		scanner := bufio.NewScanner(file)
		lineNumber := 0
		for scanner.Scan() {
			lineNumber++
			if lineNumber >= outputLastLine+1 && lineNumber <= inputLastLine {
				missingLines = append(missingLines, scanner.Text())
			}
			if lineNumber > inputLastLine {
				break
			}
		}

		for _, line := range missingLines {
			// Send each missing line into queue as normal of new VM
			if operation == "op1" {
				for _, member := range membersList.members {
					if member.DNSName == newVM {
						client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(toOp1Ports[index]))
						fmt.Fprintf(client, "op1input+"+line)
						break
					}
				}
			} else if operation == "op2" {
				for _, member := range membersList.members {
					if member.DNSName == newVM {
						client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(toOp2Ports[index]))
						fmt.Fprintf(client, "op2input+"+line)
						break
					}
				}
			}
		}
	}
}

func getLastLineNumber(filename string) int {
	file, _ := os.Open(filename)
	defer file.Close()

	scanner := bufio.NewScanner(file)
	var lastLine string
	for scanner.Scan() {
		lastLine = scanner.Text()
	}

	temp1 := strings.Split(lastLine, ":")
	temp2 := strings.Split(temp1[0], "~")

	rv, _ := strconv.Atoi(temp2[0])

	return rv
}

func reassignTasks(tasks []int, vmList []string, portList []int, logFiles []string, taskType string) {
	for _, index := range tasks {
		availableVMs := make([]string, 0, len(membersList.members))
    
		for dns := range membersList.members {
			if dns != introducerName {
				availableVMs = append(availableVMs, dns)
			}
		}
		replacement := findLeastBusyVM(availableVMs)
		vmList[index] = replacement
		replaceTask(replacement, taskType, index)
		portMappings[replacement] = append(portMappings[replacement], portList[index])
		if taskType != "source" {
			var inputLogFile string
			if taskType == "op1" {
				inputLogFile = sourceLogFiles[index]
			} else {
				inputLogFile = op1LogFiles[index]
			}
			resendMissing(inputLogFile, logFiles[index], replacement, index, taskType)
		}
	}
}

/*
 * Triggered on a VM leaving to handle re-replication
 */
func VMleft(deadVM string) {

	var allFiles []string

	if myID == 1 && rainStormStatus{
		membersList.lock.RLock()
        defer membersList.lock.RUnlock()

        // Find all tasks assigned to the dead VM
        var sourceTasks, op1Tasks, op2Tasks []int
        for i, vm := range sourceVMs {
            if vm == deadVM {
                sourceTasks = append(sourceTasks, i)
            }
        }
        for i, vm := range op1VMs {
            if vm == deadVM {
                op1Tasks = append(op1Tasks, i)
            }
        }
        for i, vm := range op2VMs {
            if vm == deadVM {
                op2Tasks = append(op2Tasks, i)
            }
        }

		reassignTasks(sourceTasks, sourceVMs, []int{8083, 8083, 8083}, sourceLogFiles, "source")
        reassignTasks(op1Tasks, op1VMs, toOp1Ports, op1LogFiles, "op1")
        reassignTasks(op2Tasks, op2VMs, toOp2Ports, op2LogFiles, "op2")

        // Clear port mappings for dead VM
        delete(portMappings, deadVM)

		membersList.lock.RUnlock()
	}

	_, err := os.Stat("DFS")
	if !os.IsNotExist(err) {
		files, _ := ioutil.ReadDir("./DFS")

		for _, file := range files {
			if !file.IsDir() {
				allFiles = append(allFiles, file.Name())
			}
		}

		/* calculate the new replicas for the file and promote the first replica VM */
		for _, dfsfileName := range allFiles {
			localFilePath := fmt.Sprintf("./DFS/%s", dfsfileName)
			os.Stat(localFilePath)
			calcID, _ := getMachineID(dfsfileName)
			actualID, VMAddress1 := getRealID(calcID)
			secondID, _ := getRealID(actualID + 1)
			thirdID, VMAddress3 := getRealID(secondID + 1)
			// _, VMAddress4 := getRealID(thirdID + 1)

			matches := dns_name_regex.FindStringSubmatch(deadVM)
			id, _ := strconv.Atoi(matches[1])

			// If primary of file failed and we are first replica (remember this is after failure)
			if id == calcID && VMAddress1 == myName {
				content, _ := os.ReadFile(localFilePath)
				createFile(dfsfileName, content, VMAddress3, 1)
			} else if VMAddress1 == myName {
				// if deadVM == VMAddress2 || deadVM == VMAddress3{
				if (thirdID > actualID) && (actualID < id && id < thirdID) {
					content, _ := os.ReadFile(localFilePath)
					createFile(dfsfileName, content, VMAddress3, 1)
				} else if thirdID < actualID { // if the new calculation wraps around to front
					if (id < thirdID) || (id > actualID) {
						content, _ := os.ReadFile(localFilePath)
						createFile(dfsfileName, content, VMAddress3, 1)
					}
				}
			}
		}
	}
}

func redistributeTasks(newVM string) {
    for i, vm := range sourceVMs {
        if len(portMappings[vm]) > len(portMappings[newVM]) + 1 {
            sourceVMs[i] = newVM
            break
        }
    }
    for i, vm := range op1VMs {
        if len(portMappings[vm]) > len(portMappings[newVM]) + 1 {
            op1VMs[i] = newVM
            replaceTask(newVM, "op1", i)
            break
        }
    }
    for i, vm := range op2VMs {
        if len(portMappings[vm]) > len(portMappings[newVM]) + 1 {
            op2VMs[i] = newVM
            replaceTask(newVM, "op2", i)
            break
        }
    }
}

/*
 * Triggered on a VM joining to reset correct parents
 */
func VMjoined(newVM string) {
	var allFiles []string

	if myID == 1  && rainStormStatus{
		membersList.lock.RLock()
        defer membersList.lock.RUnlock()

        redistributeTasks := func(vmList []string, portList []int, taskType string) {
            for i, vm := range vmList {
                if len(portMappings[vm]) > len(portMappings[newVM])+1 {
                    vmList[i] = newVM
                    deleteTask(vm, taskType, i, portList[i])
                    replaceTask(newVM, taskType, i)
                    portMappings[newVM] = append(portMappings[newVM], portList[i])
                    break
                }
            }
        }

        redistributeTasks(sourceVMs, []int{8083, 8083, 8083}, "source")
        redistributeTasks(op1VMs, toOp1Ports, "op1")
        redistributeTasks(op2VMs, toOp2Ports, "op2")
	}

	_, err := os.Stat("DFS")
	if !os.IsNotExist(err) {
		files, _ := ioutil.ReadDir("./DFS")

		for _, file := range files {
			if !file.IsDir() {
				allFiles = append(allFiles, file.Name())
			}
		}

		for _, dfsfileName := range allFiles {
			localFilePath := fmt.Sprintf("./DFS/%s", dfsfileName)
			os.Stat(localFilePath)
			calcID, _ := getMachineID(dfsfileName)

			actualID, VMAddress1 := getRealID(calcID)
			secondID, VMAddress2 := getRealID(actualID + 1)
			thirdID, VMAddress3 := getRealID(secondID + 1)
			_, VMAddress4 := getRealID(thirdID + 1)

			// If a holder of file (primary or replica) rejoined and we are last replica
			if myName != VMAddress1 && (VMAddress1 == newVM || VMAddress2 == newVM || VMAddress3 == newVM) && VMAddress4 == myName {
				content, _ := os.ReadFile(localFilePath)
				time.Sleep(2 * time.Second) // In case, wait for the server to actually be up
				createFile(dfsfileName, content, newVM, 1)
				os.Remove(localFilePath)
			}
		}
	}
}

/*
 * The main server for DFS operations. Processes incoming DFS related tasks like adding or removing files.
 * Also uses global membership list to keep track of members.
 */
func serverDFS() {
	message := make([]byte, 10000)
	udpAddress := net.UDPAddr{
		IP:   net.ParseIP(myIP),
		Port: 8081,
	}

	server, _ := net.ListenUDP("udp", &udpAddress)

	for {
		if memberRunning {
			length, remoteVM, _ := server.ReadFromUDP(message)
			received := message[:length]

			/* sending list of all DFS files that are on this machine */
			if string(received[:12]) == "needAllFiles" {
				var response string
				_, err := os.Stat("DFS")
				if !os.IsNotExist(err) {
					response += "hereAllFiles+"
					files, _ := ioutil.ReadDir("./DFS")

					for _, file := range files {
						if !file.IsDir() {
							response += file.Name() + "+"
						}
					}
				}
				server.WriteToUDP([]byte(response), remoteVM)

				/* writes to a file based on the given content */
			} else if string(received[:10]) == "writeFile+" {
				somethingElse := string(received[10:])
				payload := strings.Split(somethingElse, "+")
				dfsfileName := payload[0]
				content := payload[1]

				_, err := os.Stat("DFS")
				if os.IsNotExist(err) {
					err := os.Mkdir("DFS", 0755)
					if err != nil {
						fmt.Println("Failed to create DFS directory")
						return
					}
				}

				filePath := fmt.Sprintf("./DFS/%s", dfsfileName)
				_, err = os.Stat(filePath)
				if !os.IsNotExist(err) {
					fmt.Println("DFS file already exists, can't overwrite")
					return
				}

				info, err := os.Stat(filePath)
				startSize := 0
				if err == nil {
					startSize = int(info.Size())
				}

				// writefile is only for creating files, to append use another function
				err = os.WriteFile(filePath, []byte(content), 0644)
				if err != nil {
					fmt.Println("Error writing to DFS file")
					return
				}

				/* we want to make sure that the writes are added in this dictionary, later used for merge */
				appendDict[dfsfileName] = append(appendDict[dfsfileName], FileChange{Timestamp: string(time.Now().Format(time.RFC3339)), Start: int(startSize), Length: len(content)})
			} else if string(received[:11]) == "appendFile+" {
				somethingElse := string(received[11:])
				payload := strings.Split(somethingElse, "+")
				dfsfileName := payload[0]
				content := payload[1]

				filePath := fmt.Sprintf("./DFS/%s", dfsfileName)
				_, err := os.Stat(filePath)
				if os.IsNotExist(err) {
					fmt.Println("DFS file does not exist, cannot append")
					return
				}

				dfsFile, err := os.OpenFile(filePath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
				if err != nil {
					fmt.Println("Error opening file to append")
				}

				info, err := os.Stat(filePath)
				startSize := 0
				if err == nil {
					startSize = int(info.Size())
				}

				_, err = dfsFile.WriteString(content)
				if err != nil {
					fmt.Println("Error appending to file")
				}

				dfsFile.Close()

				/* we want to make sure that the writes are added in this dictionary, later used for merge */
				appendDict[dfsfileName] = append(appendDict[dfsfileName], FileChange{Timestamp: string(time.Now().Format(time.RFC3339)), Start: int(startSize), Length: len(content)})

				/* sends content of file that is asked for */
			} else if string(received[:9]) == "needFile+" {
				dfsfileName := string(received[9:])
				filepath := fmt.Sprintf("./DFS/%s", dfsfileName)
				file, _ := os.Open(filepath)
				content, _ := io.ReadAll(file)
				file.Close()

				payload := fmt.Sprintf("hereFile+%s+%s", dfsfileName, content)
				server.WriteToUDP([]byte(payload), remoteVM)
				/* called append all files for a particualar append */
			} else if string(received[:12]) == "multiappend+" {
				bothFiles := string(received[12:])
				payload := strings.Split(bothFiles, "+")
				dfsfileName := payload[0]
				localfileName := payload[1]

				appendAllFiles(localfileName, dfsfileName)

				server.WriteToUDP([]byte("appendworked"), remoteVM)
				/* retrives a specific VMs appendDict for a file */
			} else if string(received[:11]) == "changeHAND+" {
				dfsfileName := string(received[11:])
				fileChanges, exists := appendDict[dfsfileName]

				if exists {
					payload := ""
					for _, elem := range fileChanges {
						temp := elem.Timestamp + "~"
						temp += strconv.Itoa(elem.Start) + "~"
						temp += strconv.Itoa(elem.Length)
						payload += temp + "+"
					}

					hereChanges := fmt.Sprintf("penny+%s", payload)
					server.WriteToUDP([]byte(hereChanges), remoteVM)
				} else {
					fmt.Println("Key not found")
					return
				}
				/* ensures that the replica has been merged properly */
			} else if string(received[:9]) == "repmerge+" {
				fileAndcontent := strings.Split(string(received[9:]), "+")
				dfsfileName := fileAndcontent[0]
				content := fileAndcontent[1]

				filePath := fmt.Sprintf("./DFS/%s", dfsfileName)
				_, err := os.Stat(filePath)
				if !os.IsNotExist(err) {
					err = os.WriteFile(filePath, []byte(content), 0644)
					message := fmt.Sprintf("Replica for %s has been updated", dfsfileName)
					fmt.Println((message))
				} else {
					errorMessage := fmt.Sprintf("Replica for %s has failed to be updated", dfsfileName)
					fmt.Println((errorMessage))
				}
			} else if string(received[:10]) == "mergeFile+" {
				dfsfileName := string(received[10:])
				merge(dfsfileName)
			}
		} else {
			/* To avoid receiving requests, if we are not running (if we have left) close the server and wait */
			server.Close()
			for !memberRunning {
				time.Sleep(50 * time.Millisecond)
			}
			server, _ = net.ListenUDP("udp", &udpAddress)
		}
	}

	server.Close()
}

/* This function retrives a file from a server that is specified in the parameter */
func getFileR(VMAddress string, dfsfileName string, localfileName string) {
	content := ""
	for _, member := range membersList.members {
		if member.DNSName == VMAddress {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8081))
			payload := fmt.Sprintf("needFile+%s", dfsfileName)
			fmt.Fprintf(client, payload)

			original := make([]byte, 10000)
			length, err := bufio.NewReader(client).Read(original)
			if err == nil {
				response := original[:length]
				if string(response[:9]) == "hereFile+" {
					somethingElse := string(response[9:])
					thing := strings.Split(somethingElse, "+")
					/* makes sure what is being retrived is actually what we asked for */
					if thing[0] != dfsfileName {
						fmt.Println("This is not the correct content of file")
						return
					} else {
						content = thing[1]
					}
				}
			}
			client.Close()
			break
		}
	}

	filePath := fmt.Sprintf("./%s", localfileName)

	/* WriteFile creates a file if it doesn't exist, and always overwrites existing file */
	err := os.WriteFile(filePath, []byte(content), 0644)
	if err != nil {
		fmt.Println("Error writing to local file")
		return
	}

	completed := fmt.Sprintf("Sucessfully placed %s into %s via %s", dfsfileName, localfileName, VMAddress)
	fmt.Println(completed)
}

func lineCounter(r io.Reader) (int, error) {
	buf := make([]byte, 32*1024)
	count := 1
	delimeter := []byte{'\n'}

	for {
		c, err := r.Read(buf)
		count += bytes.Count(buf[:c], delimeter)

		if err == io.EOF {
			return count, nil
		}
		if err != nil {
			return count, err
		}
	}
}

func sourceOp(numTasks int, sourceFile string) {
	file, _ := os.Open(sourceFile)
	defer file.Close()
	lineCount, _ := lineCounter(file)
	// fmt.Println(strconv.Itoa(lineCount))

	partitionSize := lineCount / numTasks

	file.Seek(0, io.SeekStart)
	scanner := bufio.NewScanner(file)
	var lines string
	count := 0
	startLine := 1

	fmt.Println("starting loop to calculate chunks...")
	for i := 1; i < numTasks; i++ {
		// filePath := "./" + "testy" + strconv.Itoa(i) + ".txt"
		for scanner.Scan() {
			lines += scanner.Text()
			lines += "\n"
			count++
			if count == partitionSize {
				// CLIENT CALL TO SOURCE WORKER SERVER 1 and 2
				for _, member := range membersList.members {
					if member.DNSName == sourceVMs[i-1] {

						fmt.Println("sending it to %s source", member.DNSName)
						
						path := "chunk" + strconv.Itoa(i) + ".txt"
						file, _ := os.Create(path)
						defer file.Close()
						file.WriteString(lines)
						// fmt.Fprintf(workerClient, ) // TODO add lines to send to server

						go sendLine(path, sourceVMs[i-1], member.IP, sourceFile, startLine)

						startLine += count

						break
					}
				}

				lines = ""
				count = 0
				break
			}

			
		}
	}

	for scanner.Scan() {
		lines += scanner.Text()
		lines += "\n"
	}
	// CLIENT CALL TO SOURCE WORKER SERVER 3

	fmt.Println("chunk ended, sending it to third source")


	for _, member := range membersList.members {
		if member.DNSName == sourceVMs[2] {

			fmt.Println("sending it to %s source", member.DNSName)

			path := "chunk" + strconv.Itoa(3) + ".txt"
			file, _ := os.Create(path)
			defer file.Close()
			file.WriteString(lines)

			go sendLine(path, sourceVMs[2], member.IP, sourceFile, startLine)

			break
		}
	}

	


}

func sendLine(chunkFile string, sourceVM string, ip string, sourceFile string, startLine int) {

	content, _ := ioutil.ReadFile(chunkFile)
	chunk := string(content) 

	allLines := strings.Split(chunk, "\n")

	var index int
	for temp, DNSName := range sourceVMs {
		if DNSName == sourceVM {
			index = temp
			break
		}
	}

	for count, eachLine := range allLines {
		tuple := sourceFile + ":" + strconv.Itoa(startLine+count) + "~" + eachLine
		payload := strconv.Itoa(index)+"+"+tuple


		vm1Client, _ := net.Dial("udp", ip+":"+strconv.Itoa(8082))
		fmt.Fprintf(vm1Client, "workersource+"+payload)
	}
}

func firstOp(operation string, numTasks int, sourceFile string, pattern string) {
	for i := 0; i < numTasks; i++ {
		op1VM := op1VMs[i]
		for _, member := range membersList.members {
			if member.DNSName == op1VM {
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8082))
				fmt.Fprintf(client, "op1name+"+pattern+"+"+operation+"+"+strconv.Itoa(i)) // i is version of operation (btwn 0 and num_tasks)

			}
		}
	}
}

func secondOp(operation string, numTasks int, sourceFile string) {
	for i := 0; i < numTasks; i++ {
		op2VM := op2VMs[i]
		for _, member := range membersList.members {
			if member.DNSName == op2VM {
				client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(8082))
				fmt.Fprintf(client, "op2name+"+operation+"+"+strconv.Itoa(i)) // i is version of operation (btwn 0 and num_tasks)
			}
		}
	}
}

func assignVMs(numTasks int, taskType string) []string {
    var assignedVMs []string
    availableVMs := make([]string, 0, len(membersList.members))
    
    for dns := range membersList.members {
        if dns != introducerName {
            availableVMs = append(availableVMs, dns)
        }
    }

    for i := 0; i < numTasks; i++ {
        leastBusyVM := findLeastBusyVM(availableVMs)
        assignedVMs = append(assignedVMs, leastBusyVM)
        
        // Update portMappings based on the task type
        switch taskType {
        case "source":
            portMappings[leastBusyVM] = append(portMappings[leastBusyVM], 8083)
        case "op1":
            portMappings[leastBusyVM] = append(portMappings[leastBusyVM], toOp1Ports[i])
        case "op2":
            portMappings[leastBusyVM] = append(portMappings[leastBusyVM], toOp2Ports[i])
        }
        
        // Remove the assigned VM from available VMs if all ports are used
        if len(portMappings[leastBusyVM]) >= 3 {
            for j, vm := range availableVMs {
                if vm == leastBusyVM {
                    availableVMs = append(availableVMs[:j], availableVMs[j+1:]...)
                    break
                }
            }
        }
    }
    return assignedVMs
}

func findLeastBusyVM(availableVMs []string) string {
    var leastBusyVM string
    minTasks := 999

    for _, vm := range availableVMs {
        taskCount := len(portMappings[vm])
        if taskCount < minTasks {
            minTasks = taskCount
            leastBusyVM = vm
        }
    }

    return leastBusyVM
}

func rainStorm(op1 string, op2 string, sourceFile string, destFile string, numTasks int) {
	if myID == 1 {
		rainStormStatus = true

		fmt.Print("Enter pattern x: ")
		fmt.Scanln(&pattern)

		sourceVMs = assignVMs(numTasks, "source")
	
        op1VMs = assignVMs(numTasks, "op1")
		
        op2VMs = assignVMs(numTasks, "op2")

		fmt.Print("source vms ")
		fmt.Println(sourceVMs)
		fmt.Print("op1 vms ")
		fmt.Println(op1VMs)
		fmt.Print("op2 vms ")
		fmt.Println(op2VMs)
		fmt.Print("port mappings ")
		fmt.Println(portMappings)
		

		createAllFiles("blank_log.txt", "sourceoutput.log")
		createAllFiles("blank_log.txt", "op1output.log")
		createAllFiles("blank_log.txt", "finaloutput.log")

		createAllFiles(op1, op1 + ".txt")
		createAllFiles(op2, op2 + ".txt")

		sourceOp(numTasks, sourceFile)

		firstOp(op1, numTasks, sourceFile, pattern)
		secondOp(op2, numTasks, sourceFile)

	}
}

// Source worker code
// essentially a client call to the next VM
// func handleSource(sourceFile string, startLine int, chunk string, op1VM string, index int) {
// 	var ip string
// 	for _, member := range membersList.members {
// 		if member.DNSName == op1VM {
// 			ip = member.IP
// 		}
// 	}
// 	allLines := strings.Split(chunk, "\n")

// 	for count, eachLine := range allLines {

// 		tuple := "(" + sourceFile + ":" + strconv.Itoa(startLine+count) + "~" + eachLine + ")"

// 		curPort := toOp1Ports[index] // Individual ports for each worker

// 		op1Client, _ := net.Dial("udp", ip+":"+strconv.Itoa(curPort))
// 		fmt.Fprintf(op1Client, "op1input+"+tuple)

// 	}
// }

// New handleSource sends directly to VM1
func handleSource(index_tuple string) {
	vm1Client, _ := net.Dial("udp", introducerIP+":"+strconv.Itoa(8083))
	fmt.Fprintf(vm1Client, "sourceoutput+" + index_tuple)
}

func workerServer() {
	message := make([]byte, 100000000)
	udpAddress := net.UDPAddr{
		IP:   net.ParseIP(myIP),
		Port: 8082,
	}

	server, _ := net.ListenUDP("udp", &udpAddress)

	fmt.Println(" Started as worker")

	var cmd1_1 *exec.Cmd
	var cmd1_1v int

	var cmd1_2 *exec.Cmd
	var cmd1_2v int

	var cmd2_1 *exec.Cmd
	var cmd2_1v int

	var cmd2_2 *exec.Cmd
	var cmd2_2v int

	for {
		if memberRunning {
			fmt.Println("member running?")

			length, remoteVM, _ := server.ReadFromUDP(message)
			received := message[:length]

			fmt.Println(" Received data")

			if string(received[:13]) == "workersource+" {
				// Worker receives message from leader to start as a source worker

				fmt.Println(" I AM SOURCE")

				index_tuple := string(received[13:])

				fmt.Println("got data" + index_tuple)
				handleSource(index_tuple)

			}

			if string(received[:7]) == "op1name" {

				fmt.Println(" I AM OP1")

				somethingElse := string(received[7:])
				payload := strings.Split(somethingElse, "+")

				x_pattern := payload[0]
				operation := payload[1]
				version := payload[2]
				int_version, _ := strconv.Atoi(version)

				pattern = x_pattern

				operation1 = operation

				getFile(operation + ".txt", operation) // Use the Operation exec binaries, no need for "go build"
				cmd := exec.Command("./"+operation, version, myIP, x_pattern, strconv.Itoa(toOp1Ports[int_version]))
				cmd.Run()
				// output, _ := cmd.Output()

				// vm1Client, _ := net.Dial("udp", introducerIP+":"+strconv.Itoa(8083))
				// fmt.Fprintf(vm1Client, "op1output+"+string(output))
			}

			if string(received[:7]) == "op2name" {

				fmt.Println(" I AM OP2")

				somethingElse := string(received[7:])
				payload := strings.Split(somethingElse, "+")

				operation := payload[0]
				version := payload[1]
				int_version, _ := strconv.Atoi(version)

				operation2 = operation

				getFile(operation + ".txt", operation)
				// exec.Command("go", "build", operation)
				cmd := exec.Command("./"+operation, version, myIP, strconv.Itoa(toOp1Ports[int_version]))
				cmd.Run()

				// vm1Client, _ := net.Dial("udp", introducerIP+":"+strconv.Itoa(8083))
				// fmt.Fprintf(vm1Client, "op2output+"+string(output))
			}

			if string(received[:12]) == "replaceTask+" {
				somethingElse := string(received[12:])
				payload := strings.Split(somethingElse, "+")

				operation := payload[0]
				version := payload[1]

				if operation == "op1" {
					operation = operation1
					if cmd1_1 == nil {
						cmd1_1v, _ = strconv.Atoi(version)
						cmd1_1 = exec.Command("./"+operation, version, myIP, pattern)
						cmd1_1.Run()
					} else if cmd1_2 == nil {
						cmd1_2v, _ = strconv.Atoi(version)
						cmd1_2 = exec.Command("./"+operation, version, myIP, pattern)
						cmd1_2.Run()
					}

				} else if operation == "op2" {
					operation = operation2
					if cmd2_1 == nil {
						cmd2_1v, _ = strconv.Atoi(version)
						cmd2_1 = exec.Command("./"+operation, version, myIP)
						cmd2_1.Run()
					} else if cmd2_2 == nil {
						cmd2_2v, _ = strconv.Atoi(version)
						cmd2_2 = exec.Command("./"+operation, version, myIP)
						cmd2_2.Run()
					}

				}

			}

			if string(received[:11]) == "deleteTask+" {
				somethingElse := string(received[11:])
				payload := strings.Split(somethingElse, "+")

				operation := payload[0]
				version, _ := strconv.Atoi(payload[1])

				if operation == "op1" {
					if cmd1_1v == version {
						process := cmd1_1.Process
						if err := process.Kill(); err != nil {
							log.Fatalf("Failed to kill process: %v", err)
						}

					} else if cmd1_2v == version {
						process := cmd1_2.Process
						if err := process.Kill(); err != nil {
							log.Fatalf("Failed to kill process: %v", err)
						}
					}
				} else if operation == "op2" {
					if cmd2_1v == version {
						process := cmd2_1.Process
						if err := process.Kill(); err != nil {
							log.Fatalf("Failed to kill process: %v", err)
						}

					} else if cmd2_2v == version {
						process := cmd2_2.Process
						if err := process.Kill(); err != nil {
							log.Fatalf("Failed to kill process: %v", err)
						}
					}
				}

				server.WriteToUDP([]byte("startedProcess+"), remoteVM)
			}
		}
	}

	server.Close()
}

func dataRoutingServer() {
	message := make([]byte, 100000)
	if myID != 1 {
		return // Only run on VM1
	}

	udpAddress := net.UDPAddr{
		IP:   net.ParseIP(myIP),
		Port: 8083,
	}

	server, _ := net.ListenUDP("udp", &udpAddress)

	for {
		length, _, _ := server.ReadFromUDP(message)
		received := message[:length]

		if string(received[:13]) == "sourceoutput+" {
			
			somethingElse := string(received[13:])
			payload := strings.Split(somethingElse, "+")
			version, _ := strconv.Atoi(payload[0])
			tuple := payload[1]
			fmt.Println(tuple)
			handleSourceOutput(tuple, version)
		} else if string(received[:10]) == "op1output+" {
			somethingElse := string(received[10:])
			payload := strings.Split(somethingElse, "+")
			version, _ := strconv.Atoi(payload[0])
			output := payload[1]
			handleOp1Output(output, version)
		} else if string(received[:10]) == "op2output+" {
			somethingElse := string(received[10:])
			payload := strings.Split(somethingElse, "+")
			version, _ := strconv.Atoi(payload[0])
			output := payload[1]
			handleOp2Output(output, version)
		}
	}

	server.Close()
}

func handleSourceOutput(data string, version int) {
	// Log to DFS

	filepath := "temp.log"
	temp, _ := os.Create(filepath)
	defer temp.Close()
	temp.WriteString(data + "\n")
	defer os.Remove(filepath)

	appendAllFiles(filepath, "sourceoutput.log") //TODO create the output log files in first place
	file, err := os.OpenFile(sourceLogFiles[version], os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		fmt.Println("Couldn't open file")
	}
	defer file.Close()
	file.WriteString(data)

	// Forward to Op1 VM (or rerouted VM on failures)
	op1VM := op1VMs[version]

	// Check if port has been moved due to failure
	found := false
	for name, ports := range portMappings {
		for _, val := range ports {
			if val == toOp1Ports[version] {
				op1VM = name
				found = true
				break
			}
		}
		if found {
			break
		}
	}

	// TODO: on failure of a VM, version needs to be changed
	for _, member := range membersList.members {
		if member.DNSName == op1VM {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(toOp1Ports[version]))
			fmt.Fprintf(client, "op1input+"+data)
			break
		}
	}
}

func handleOp1Output(data string, version int) {
	// Log to DFS
	appendAllFiles("op1output.log", data)
	file, err := os.OpenFile(op1LogFiles[version], os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		fmt.Println("Couldn't open file")
	}
	defer file.Close()
	file.WriteString(data)

	// Forward to Op2 VM
	op2VM := op2VMs[version]

	// Check if port has been moved due to failure
	found := false
	for name, ports := range portMappings {
		for _, val := range ports {
			if val == toOp2Ports[version] {
				op2VM = name
				found = true
				break
			}
		}
		if found {
			break
		}
	}

	for _, member := range membersList.members {
		if member.DNSName == op2VM {
			client, _ := net.Dial("udp", member.IP+":"+strconv.Itoa(toOp2Ports[version]))
			fmt.Fprintf(client, "op2input+"+data)
			break
		}
	}
}

func handleOp2Output(data string, version int) {

	fields := strings.Split(data, "~")
	if strings.Contains(fields[1], ":") { // check if needs to be aggregated
		_, existing := categoryCount[strconv.Itoa(version)]
		if !existing {
            categoryCount[strconv.Itoa(version)] = make(map[string]int) //intitialize the mini maps
        }
		categories := strings.Split(fields[1], ",")
		for _, category_val := range categories {
			values := strings.Split(category_val, ":")
			//values[0] is category
			category := strings.TrimSpace(values[0])
			//values[1] is val
            count, _ := strconv.Atoi(strings.TrimSpace(values[1]))
			categoryCount[strconv.Itoa(version)][category] = count
			
		}
		totalCounts := make(map[string]int)
        for _, versionCounts := range categoryCount {
            for category, count := range versionCounts {
                totalCounts[category] += count
            }
        }

		aggregatedOutput := ""
		for category, total := range totalCounts {
			aggregatedOutput += fmt.Sprintf("%s:%d,", category, total)
		}
		data = strings.TrimRight(aggregatedOutput, ",")
	}

	appendAllFiles("finaloutput.log", data)
	file, err := os.OpenFile(op2LogFiles[version], os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		fmt.Println("Couldn't open file")
	}
	defer file.Close()
	file.WriteString(data)
	fmt.Println("Final Output:", data)
}

/* This function handles the inputs given by the user  */
func handleInputs() {
	reader := bufio.NewReader(os.Stdin)
	for {
		original, _ := reader.ReadString('\n')
		original = strings.TrimRight(original, "\n")

		present := false
		_, ok := membersList.members[myName]
		if ok {
			present = true
		}

		/* Following commands can be typed when programs are running */
		command := strings.Split(original, " ")
		if command[0] == "join" {
			if !present {
				introduce()
			}
		} else if command[0] == "leave" {
			Remove(&membersList, myName)
			memberRunning = false
		} else if command[0] == "list_mem" {
			allMembers := Get(&membersList)
			for _, value := range allMembers {
				fmt.Println(value)
			}
		} else if command[0] == "list_mem_ids" {
			listMemIds()
		} else if command[0] == "list_self" {
			member := membersList.members[myName]
			fmt.Println(member)
		} else if command[0] == "enable_sus" {
			status_sus = true
			fmt.Println("Enabled Suspicion")
		} else if command[0] == "disable_sus" {
			status_sus = false
			fmt.Println("Disabled Suspicion")
		} else if command[0] == "status_sus" {
			fmt.Println(status_sus)
		} else if command[0] == "create" {
			createAllFiles(command[1], command[2])
		} else if command[0] == "get" {
			getFile(command[1], command[2])
		} else if command[0] == "getfromreplica" {
			getFileR(command[1], command[2], command[3])
		} else if command[0] == "ls" {
			lsFile(command[1])
		} else if command[0] == "storeAll" {
			storeFileAll()
		} else if command[0] == "store" {
			storeFile()
		} else if command[0] == "append" {
			appendAllFiles(command[1], command[2])
		} else if command[0] == "multiappend" {
			numAppends := (len(command) - 2) / 2
			if len(command[2:2+numAppends]) != len(command[2+numAppends:]) {
				fmt.Println("Number of localfiles are not equal to number of VMs")
			} else {
				multiAppend(command[1], command[2:2+numAppends], command[2+numAppends:])
			}
		} else if command[0] == "printDict" {
			fmt.Println(appendDict)
		} else if command[0] == "merge" {
			merge(command[1])
		} else if command[0] == "Rainstorm" {
			num_tasks, _ := strconv.Atoi(command[5])
			if myID == 1 {
				rainStorm(command[1], command[2], command[3], command[4], num_tasks)
			}
		} else {
			fmt.Println("Command not recognized: " + original)
		}
	}
}

/* This function is called when a new process joins, it communicates with the introducer
 * with some information and only once the introducer sends an ack, does the process
 * in question update its fields with the correct version number.
 */
func introduce() {
	me := Member{
		DNSName:   myName,
		IP:        myIP,
		Timestamp: time.Now().Format(time.RFC3339),
		Version:   -1,
		Port:      myPort,
	}

	// On introduce clear local DFS files
	dirPath := "DFS"
	_, err := os.Stat(dirPath)
	if err == nil {
		os.RemoveAll(dirPath)
		// time.Sleep(1 * time.Second)
	}

	/* sending potential values to introducer, which will be updated actually once ack is received */
	_, exists := membersList.versions[myName]
	if exists {
		me.Version = membersList.versions[myName] + 1
	} else {
		me.Version = 0
	}

	/* sending a message to introducer, asking to join */
	client, _ := net.Dial("udp", introducerIP+":"+strconv.Itoa(introducerPort))

	memberString := fmt.Sprintf("%s+%s+%s+%d+%d+join", me.DNSName, me.IP, me.Timestamp, me.Version, me.Port)
	fmt.Fprintf(client, "ping+%s", memberString)

	if exists {
		me.Version = membersList.versions[myName]
	}

	response := make([]byte, 10000)
	_, err = bufio.NewReader(client).Read(response)
	if err == nil {
		if string(response[:3]) == "ack" {
			fmt.Println("Successfully received " + string(response[:3]))
			/* if ack is received then we increment our versions, else, we set it to 0 - after sucessful join */
			_, exists := membersList.versions[myName]
			if exists {
				membersList.versions[myName]++
				me.Version = membersList.versions[myName] + 1
			} else {
				membersList.versions[myName] = 0
				membersList.incars[myName] = 0
			}

			Add(&membersList, me)
			memberRunning = true
		} else {
			fmt.Printf("Could not introduce, ack not received")
		}
	} else {
		fmt.Printf("Could not introduce, introducer is down")
	}
	client.Close()
}

func main() {
	status_sus = false
	mergeOK = false
	rainStormStatus = false
	/* clearing the log file */
	files, _ := os.ReadDir(".")
	for _, file := range files {
		if !file.IsDir() && strings.HasPrefix(file.Name(), "machine") {
			logFile, _ := os.OpenFile(file.Name(), os.O_WRONLY|os.O_TRUNC, 0644)
			logFile.Close()
			break
		}

	}

	/* Initalizing the memberslist */
	membersList = MembershipList{
		members: map[string]Member{
			introducerName: {
				DNSName:   introducerName,
				IP:        introducerIP,
				Timestamp: time.Now().Format(time.RFC3339),
				Version:   0,
				Port:      introducerPort,
			},
		},
		versions: map[string]int{
			introducerName: 0,
		},
		incars: map[string]int{
			introducerName: 0,
		},
		lock: sync.RWMutex{},
	}

	memberRunning = false

	var allMembers []Member

	go server()
	go serverDFS()
	go handleInputs()
	if myID != 1 {
		go workerServer()
	}
	if myID == 1 {
		go dataRoutingServer()
	}

	/* Starting the threads and starting client */
	for {
		if memberRunning {
			allMembers = Get(&membersList)
			randMember := allMembers[rand.Intn(len(allMembers))]
			if status_sus {
				go susClient(randMember.IP, randMember.Port, randMember.DNSName)
			} else {
				go client(randMember.IP, randMember.Port, randMember.DNSName)
			}
		}
		time.Sleep(500 * time.Millisecond)
	}

	select {}
}

// add worker source to main
