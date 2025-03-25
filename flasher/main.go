package main

import (
	"bufio"
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"syscall"
	"time"

	"golang.org/x/crypto/pbkdf2"
	"golang.org/x/term"
)

const (
	defaultPoolFile = "mac_pool.enc" // Имя зашифрованного файла с пулом MAC-адресов
	saltSize        = 16             // Размер соли для PBKDF2
	keySize         = 32             // Размер ключа AES-256
	iterations      = 10000          // Количество итераций для PBKDF2
	maxRetries      = 3              // Максимальное число попыток для критических операций
)

var (
	cDir        string // текущая рабочая директория
	mac         string // MAC-адрес из пула
	rtDrv       string // имя удалённого конфликтующего драйвера
	productName string // имя продукта из dmidecode

	// Параметры
	poolFilePath string // путь к файлу с пулом MAC-адресов
	noReboot     bool   // флаг для отключения автоматической перезагрузки
	logToFile    bool   // флаг для сохранения лога в файл
	logServer    string // адрес сервера для отправки лога (формат: user@host:path)
)

// ANSI escape sequences для цветного вывода
const (
	colorReset   = "\033[0m"
	colorRed     = "\033[31m"
	colorGreen   = "\033[32m"
	colorYellow  = "\033[33m"
	colorBlue    = "\033[34m"
	colorCyan    = "\033[36m"
	colorBgRed   = "\033[41m"
	colorBgGreen = "\033[42m"
)

// MACPool содержит пул MAC-адресов и метаданные
type MACPool struct {
	Version         int          `json:"version"`
	Addresses       []MACAddress `json:"addresses"`
	LastUpdated     time.Time    `json:"last_updated"`
	CreatedBy       string       `json:"created_by"`
	Signature       string       `json:"signature,omitempty"` // HMAC подпись
	MACVendorPrefix string       `json:"mac_vendor_prefix,omitempty"`
}

// MACAddress представляет MAC-адрес и его статус
type MACAddress struct {
	Address  string    `json:"address"`
	Used     bool      `json:"used"`
	UsedAt   time.Time `json:"used_at,omitempty"`
	UsedBy   string    `json:"used_by,omitempty"`
	Reserved bool      `json:"reserved,omitempty"`
	Comment  string    `json:"comment,omitempty"`
}

// LogData структура для хранения информации о процессе
type LogData struct {
	Timestamp       string                 `json:"timestamp"`
	ProductName     string                 `json:"product_name"`
	MacAddress      string                 `json:"mac_address"`
	ActionPerformed string                 `json:"action_performed"`
	Success         bool                   `json:"success"`
	SystemInfo      map[string]interface{} `json:"system_info"`
	HostInfo        map[string]string      `json:"host_info"`
}

func main() {
	// Определение флагов командной строки
	poolFilePtr := flag.String("pool", defaultPoolFile, "Path to encrypted MAC address pool file")
	noRebootPtr := flag.Bool("no-reboot", false, "Do not reboot after MAC address flash")
	logFilePtr := flag.Bool("log", true, "Save log to file")
	logServerPtr := flag.String("server", "", "Server to send log to (format: user@host:path)")
	flag.Parse()

	poolFilePath = *poolFilePtr
	noReboot = *noRebootPtr
	logToFile = *logFilePtr
	logServer = *logServerPtr

	// Проверка прав root
	if os.Geteuid() != 0 {
		criticalError("Please run this program with root privileges")
		os.Exit(1)
	}

	var err error
	cDir, err = os.Getwd()
	if err != nil {
		criticalError("Could not get current directory: " + err.Error())
		os.Exit(1)
	}

	fmt.Println(colorBlue + "Starting MAC address flashing tool..." + colorReset)
	fmt.Println(colorBlue + "----------------------------------------" + colorReset)

	// Получение имени продукта
	productName, err = getProductName()
	if err != nil {
		fmt.Printf(colorYellow+"[WARNING] Could not get product name: %v. Using 'Unknown'.\n"+colorReset, err)
		productName = "Unknown"
	} else {
		fmt.Printf("Product Name: %s\n", productName)
	}

	// Проверка наличия файла пула
	if _, err := os.Stat(poolFilePath); os.IsNotExist(err) {
		criticalError(fmt.Sprintf("MAC address pool file %s does not exist", poolFilePath))
		os.Exit(1)
	}

	// Получение MAC-адреса из пула
	pool, password, err := loadAndDecryptPool(poolFilePath)
	if err != nil {
		criticalError("Failed to load MAC address pool: " + err.Error())
		os.Exit(1)
	}

	mac, err = getAvailableMACFromPool(pool)
	if err != nil {
		criticalError("Failed to get available MAC address: " + err.Error())
		os.Exit(1)
	}

	fmt.Printf("Selected MAC address: %s\n", mac)

	// Проверяем, не установлен ли уже указанный MAC
	targetMAC := strings.ToLower(mac)
	macAlreadySet := false
	var existingInterfaces []string

	if ifaces, err := getInterfacesWithMAC(targetMAC); err == nil && len(ifaces) > 0 {
		macAlreadySet = true
		existingInterfaces = ifaces
		fmt.Printf(colorGreen+"MAC %s is already present on interfaces: %s\n"+colorReset, targetMAC, strings.Join(ifaces, ", "))
	} else {
		fmt.Printf("MAC %s not found in system, flashing is required\n", targetMAC)
	}

	// Переменная для записи выполненных действий
	actionPerformed := ""
	success := true

	// Обработка различных сценариев
	if macAlreadySet {
		// CASE 1: MAC уже соответствует - изменения не требуются
		actionPerformed = "No changes required"
		successMessage("No reflash required – system already has the correct MAC address")

		// Обновляем статус MAC-адреса в пуле
		markMACAsUsed(pool, mac, &existingInterfaces)

		// Сохраняем обновленный пул
		updatePool(pool, password, poolFilePath)

		// Создание лога перед завершением
		createOperationLog(actionPerformed, success)

		// Предлагаем перезагрузить систему
		if !noReboot {
			reader := bufio.NewReader(os.Stdin)
			fmt.Print("Reboot system now? (Y/n): ")
			choice, _ := reader.ReadString('\n')
			choice = strings.TrimSpace(choice)
			if !strings.EqualFold(choice, "n") {
				fmt.Println("Rebooting system...")
				_ = runCommandNoOutput("reboot")
			} else {
				fmt.Println("Exiting without reboot.")
			}
		}
		return
	}

	// CASE 2: MAC требует обновления
	actionPerformed = "MAC address update"
	fmt.Println(colorYellow + "MAC address flash is required." + colorReset)

	// Пытаемся обновить MAC через драйвер с повторными попытками
	if err := writeMAcWithRetries(mac); err != nil {
		success = false
		criticalError("MAC address could not be written after multiple attempts. It is recommended to power off the system and diagnose the hardware manually.")

		// Создаём лог перед выходом
		createOperationLog("MAC address update failed", false)

		os.Exit(1)
	}

	// Обновляем статус MAC-адреса в пуле
	// Получаем список интерфейсов с новым MAC
	var updatedInterfaces []string
	if ifaces, err := getInterfacesWithMAC(targetMAC); err == nil && len(ifaces) > 0 {
		updatedInterfaces = ifaces
	}

	markMACAsUsed(pool, mac, &updatedInterfaces)

	// Сохраняем обновленный пул
	updatePool(pool, password, poolFilePath)

	// Создаём лог
	createOperationLog(actionPerformed, success)

	if success {
		successMessage("MAC address updated successfully")
	}

	// Предлагаем перезагрузить систему
	if !noReboot {
		reader := bufio.NewReader(os.Stdin)
		fmt.Print("Reboot system now? (Y/n): ")
		choice, _ := reader.ReadString('\n')
		choice = strings.TrimSpace(choice)
		if !strings.EqualFold(choice, "n") {
			fmt.Println("Rebooting system...")
			_ = runCommandNoOutput("reboot")
		} else {
			fmt.Println("Exiting without reboot.")
		}
	}
}

// updatePool обновляет и сохраняет пул с обновленной подписью
func updatePool(pool MACPool, password, poolFilePath string) error {
	// Обновляем HMAC подпись
	signPool(&pool, password)

	// Сохраняем обновленный пул
	err := saveEncryptedPool(pool, password, poolFilePath)
	if err != nil {
		fmt.Printf(colorYellow+"[WARNING] Failed to update MAC pool: %v\n"+colorReset, err)
		return err
	}

	return nil
}

// debugPrint выводит отладочную информацию
func debugPrint(message string) {
	fmt.Println(colorCyan + "DEBUG: " + message + colorReset)
}

// criticalError выводит критическую ошибку в форматированном виде
func criticalError(message string) {
	// Создаем рамку для большей заметности
	lineLength := len(message) + 6 // добавляем отступы
	if lineLength < 80 {
		lineLength = 80 // минимальная ширина плашки
	}

	border := strings.Repeat("!", lineLength)
	spaces := strings.Repeat(" ", (lineLength-len(message)-2)/2)

	fmt.Println("")
	fmt.Println(colorBgRed + colorReset)
	fmt.Println(colorBgRed + border + colorReset)
	fmt.Println(colorBgRed + "!!!" + spaces + message + spaces + "!!!" + colorReset)
	fmt.Println(colorBgRed + border + colorReset)
	fmt.Println(colorBgRed + colorReset)
	fmt.Println("")
}

// successMessage выводит информацию об успешном завершении
func successMessage(message string) {
	// Создаем рамку для большей заметности
	lineLength := len(message) + 6 // добавляем отступы
	if lineLength < 60 {
		lineLength = 60 // минимальная ширина плашки
	}

	border := strings.Repeat("=", lineLength)
	spaces := strings.Repeat(" ", (lineLength-len(message)-2)/2)

	fmt.Println("")
	fmt.Println(colorBgGreen + colorReset)
	fmt.Println(colorBgGreen + border + colorReset)
	fmt.Println(colorBgGreen + "  " + spaces + message + spaces + "  " + colorReset)
	fmt.Println(colorBgGreen + border + colorReset)
	fmt.Println(colorBgGreen + colorReset)
	fmt.Println("")
}

// getProductName получает имя продукта из выхода dmidecode
func getProductName() (string, error) {
	output, err := runCommand("dmidecode", "-t", "system")
	if err != nil {
		return "", fmt.Errorf("dmidecode failed: %v", err)
	}
	for _, line := range strings.Split(output, "\n") {
		if strings.Contains(line, "Product Name") {
			parts := strings.SplitN(line, ":", 2)
			if len(parts) == 2 {
				return strings.TrimSpace(parts[1]), nil
			}
		}
	}
	return "", errors.New("could not determine Product Name")
}

// getAvailableMACFromPool получает доступный MAC-адрес из пула
func getAvailableMACFromPool(pool MACPool) (string, error) {
	// Поиск неиспользуемого MAC-адреса
	for _, addr := range pool.Addresses {
		if !addr.Used && !addr.Reserved {
			return addr.Address, nil
		}
	}

	return "", errors.New("no available MAC addresses in pool")
}

// markMACAsUsed помечает MAC-адрес как использованный в пуле
func markMACAsUsed(pool MACPool, macAddress string, interfaces *[]string) {
	// Поиск MAC-адреса в пуле
	for i, addr := range pool.Addresses {
		if strings.EqualFold(addr.Address, macAddress) {
			hostname, _ := os.Hostname()
			pool.Addresses[i].Used = true
			pool.Addresses[i].UsedAt = time.Now()

			// Добавляем имя хоста и интерфейсы в комментарий
			interfaceStr := ""
			if interfaces != nil && len(*interfaces) > 0 {
				interfaceStr = " on " + strings.Join(*interfaces, ",")
			}
			pool.Addresses[i].UsedBy = fmt.Sprintf("%s%s", hostname, interfaceStr)
			return
		}
	}
}

// loadAndDecryptPool загружает и дешифрует пул MAC-адресов
func loadAndDecryptPool(poolFilePath string) (MACPool, string, error) {
	var pool MACPool

	// Проверка существования файла
	if _, err := os.Stat(poolFilePath); os.IsNotExist(err) {
		return pool, "", errors.New("MAC address pool file does not exist")
	}

	// Чтение зашифрованных данных
	encryptedData, err := os.ReadFile(poolFilePath)
	if err != nil {
		return pool, "", fmt.Errorf("failed to read MAC pool file: %v", err)
	}

	// Запрос пароля для дешифрования
	fmt.Print("Enter encryption password: ")
	password, err := term.ReadPassword(int(syscall.Stdin))
	fmt.Println()
	if err != nil {
		return pool, "", fmt.Errorf("failed to read password: %v", err)
	}

	// Дешифрование данных
	decryptedData, err := decrypt(encryptedData, string(password))
	if err != nil {
		return pool, "", fmt.Errorf("failed to decrypt MAC pool: %v", err)
	}

	// Разбор JSON
	if err := json.Unmarshal(decryptedData, &pool); err != nil {
		return pool, "", fmt.Errorf("failed to parse MAC pool data: %v", err)
	}

	// Проверка подписи
	if !verifyPoolSignature(&pool, string(password)) {
		return pool, "", errors.New("integrity check failed: the pool file may have been tampered with")
	}

	return pool, string(password), nil
}

// saveEncryptedPool шифрует и сохраняет пул MAC-адресов
func saveEncryptedPool(pool MACPool, password, poolFilePath string) error {
	// Сохраняем исходный файл как резервную копию
	backupPath := poolFilePath + ".bak"
	if _, err := os.Stat(poolFilePath); err == nil {
		if err := os.Rename(poolFilePath, backupPath); err != nil {
			fmt.Printf(colorYellow+"[WARNING] Failed to create backup of pool file: %v\n"+colorReset, err)
		}
	}

	// Преобразование в JSON
	data, err := json.MarshalIndent(pool, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to encode MAC pool data: %v", err)
	}

	// Шифрование данных
	encryptedData, err := encrypt(data, password)
	if err != nil {
		return fmt.Errorf("failed to encrypt MAC pool: %v", err)
	}

	// Сохранение во временный файл
	tempFile, err := os.CreateTemp(filepath.Dir(poolFilePath), "macpool-*.tmp")
	if err != nil {
		return fmt.Errorf("failed to create temporary file: %v", err)
	}
	tempFilePath := tempFile.Name()

	if _, err := tempFile.Write(encryptedData); err != nil {
		tempFile.Close()
		os.Remove(tempFilePath)
		return fmt.Errorf("failed to write to temporary file: %v", err)
	}
	tempFile.Close()

	// Переименовываем временный файл в целевой
	if err := os.Rename(tempFilePath, poolFilePath); err != nil {
		os.Remove(tempFilePath)
		return fmt.Errorf("failed to rename temporary file to pool file: %v", err)
	}

	// Устанавливаем разрешения
	if err := os.Chmod(poolFilePath, 0600); err != nil {
		fmt.Printf(colorYellow+"[WARNING] Failed to set permissions on pool file: %v\n"+colorReset, err)
	}

	return nil
}

// signPool добавляет HMAC подпись в структуру пула
func signPool(pool *MACPool, password string) {
	// Очищаем предыдущую подпись
	pool.Signature = ""

	// Создаем временную копию без подписи для вычисления хеша
	data, _ := json.Marshal(pool)

	// Создаем HMAC
	h := hmac.New(sha256.New, []byte(password))
	h.Write(data)

	// Устанавливаем подпись
	pool.Signature = hex.EncodeToString(h.Sum(nil))
}

// verifyPoolSignature проверяет HMAC подпись пула
func verifyPoolSignature(pool *MACPool, password string) bool {
	// Если подписи нет, считаем пул старой версии
	if pool.Signature == "" {
		return true
	}

	// Сохраняем оригинальную подпись
	originalSignature := pool.Signature

	// Очищаем подпись для вычисления хеша
	pool.Signature = ""

	// Создаем временную копию без подписи
	data, _ := json.Marshal(pool)

	// Создаем HMAC
	h := hmac.New(sha256.New, []byte(password))
	h.Write(data)
	expectedSignature := hex.EncodeToString(h.Sum(nil))

	// Восстанавливаем оригинальную подпись
	pool.Signature = originalSignature

	// Проверяем совпадение подписей
	return hmac.Equal([]byte(originalSignature), []byte(expectedSignature))
}

// encrypt шифрует данные с использованием AES-GCM
func encrypt(data []byte, passphrase string) ([]byte, error) {
	// Генерация соли
	salt := make([]byte, saltSize)
	if _, err := io.ReadFull(rand.Reader, salt); err != nil {
		return nil, err
	}

	// Генерация ключа из пароля с использованием соли
	key := pbkdf2.Key([]byte(passphrase), salt, iterations, keySize, sha256.New)

	// Создание шифра AES
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	// Создание GCM (Galois/Counter Mode)
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, err
	}

	// Генерация nonce (number used once)
	nonce := make([]byte, gcm.NonceSize())
	if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
		return nil, err
	}

	// Шифрование данных
	ciphertext := gcm.Seal(nil, nonce, data, nil)

	// Формат: соль + nonce + шифротекст
	result := make([]byte, 0, len(salt)+len(nonce)+len(ciphertext))
	result = append(result, salt...)
	result = append(result, nonce...)
	result = append(result, ciphertext...)

	// Кодирование в base64 для удобства хранения
	return []byte(base64.StdEncoding.EncodeToString(result)), nil
}

// decrypt дешифрует данные с использованием AES-GCM
func decrypt(encryptedData []byte, passphrase string) ([]byte, error) {
	// Декодирование из base64
	data, err := base64.StdEncoding.DecodeString(string(encryptedData))
	if err != nil {
		return nil, err
	}

	// Проверка минимальной длины
	if len(data) < saltSize {
		return nil, errors.New("encrypted data is too short")
	}

	// Извлечение соли (первые saltSize байт)
	salt := data[:saltSize]
	data = data[saltSize:]

	// Генерация ключа из пароля с использованием соли
	key := pbkdf2.Key([]byte(passphrase), salt, iterations, keySize, sha256.New)

	// Создание шифра AES
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}

	// Создание GCM (Galois/Counter Mode)
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, err
	}

	// Проверка минимальной длины
	nonceSize := gcm.NonceSize()
	if len(data) < nonceSize {
		return nil, errors.New("encrypted data is too short")
	}

	// Извлечение nonce и шифротекста
	nonce := data[:nonceSize]
	ciphertext := data[nonceSize:]

	// Дешифрование
	plaintext, err := gcm.Open(nil, nonce, ciphertext, nil)
	if err != nil {
		return nil, err
	}

	return plaintext, nil
}

// Function to create and save operation log
func createOperationLog(action string, success bool) {
	fmt.Println(colorBlue + "Creating operation log..." + colorReset)

	// Get full dmidecode output for system info
	dmidecodeOutput, err := runCommand("dmidecode")
	if err != nil {
		fmt.Printf(colorYellow+"[WARNING] Could not get dmidecode output for log: %v"+colorReset, err)
		dmidecodeOutput = "Error getting dmidecode output"
	}

	// Parse dmidecode output to get system info
	systemInfo := parseDmidecodeToMap(dmidecodeOutput)

	// Collect host info
	hostInfo := map[string]string{
		"hostname": "unknown",
		"kernel":   "unknown",
		"arch":     "unknown",
		"uptime":   "unknown",
	}

	if hostname, err := os.Hostname(); err == nil {
		hostInfo["hostname"] = hostname
	}

	if kernel, err := runCommand("uname", "-r"); err == nil {
		hostInfo["kernel"] = strings.TrimSpace(kernel)
	}

	if arch, err := runCommand("uname", "-m"); err == nil {
		hostInfo["arch"] = strings.TrimSpace(arch)
	}

	if uptime, err := runCommand("uptime"); err == nil {
		hostInfo["uptime"] = strings.TrimSpace(uptime)
	}

	// Create log data structure
	timestamp := time.Now().Format("2006-01-02T15:04:05")
	logData := LogData{
		Timestamp:       timestamp,
		ProductName:     productName,
		MacAddress:      mac,
		ActionPerformed: action,
		Success:         success,
		SystemInfo:      systemInfo,
		HostInfo:        hostInfo,
	}

	// Convert to JSON
	jsonData, err := json.MarshalIndent(logData, "", "  ")
	if err != nil {
		fmt.Printf(colorYellow+"[WARNING] Could not create JSON log: %v"+colorReset, err)
		return
	}

	// Generate filename for the log
	timeFormat := time.Now().Format("060102_150405") // YYMMDDHHMMSS
	filename := fmt.Sprintf("%s_MAC-%s_%s.json", productName, strings.ReplaceAll(mac, ":", ""), timeFormat)

	// Save log to file if flag is set
	if logToFile {
		logDir := filepath.Join(cDir, "logs")
		// Create log directory if it doesn't exist
		if _, err := os.Stat(logDir); os.IsNotExist(err) {
			if err := os.Mkdir(logDir, 0755); err != nil {
				fmt.Printf(colorYellow+"[WARNING] Could not create log directory: %v. "+colorReset, err)
				logDir = cDir
			}
		}

		logPath := filepath.Join(logDir, filename)
		if err := os.WriteFile(logPath, jsonData, 0644); err != nil {
			fmt.Printf(colorYellow+"[WARNING] Could not write log file: %v.\n"+colorReset, err)
		} else {
			fmt.Printf(colorGreen+"[INFO] Log saved to: %s\n"+colorReset, logPath)
		}
	}

	// Send log to server if specified
	if logServer != "" {
		// Create temporary file
		tempFile, err := os.CreateTemp("", "mac-log-*.json")
		if err != nil {
			fmt.Printf(colorYellow+"[WARNING] Could not create temporary file for log: %v"+colorReset, err)
			return
		}

		// Write JSON to file
		if _, err := tempFile.Write(jsonData); err != nil {
			fmt.Printf(colorYellow+"[WARNING] Could not write to temporary file: %v"+colorReset, err)
			tempFile.Close()
			os.Remove(tempFile.Name())
			return
		}
		tempFile.Close()

		// Parse server string to host and path
		var host, remotePath string
		parts := strings.SplitN(logServer, ":", 2)

		host = parts[0]
		if len(parts) > 1 {
			remotePath = parts[1]
		}

		// Build correct path for SCP
		var destination string
		if remotePath != "" {
			destination = fmt.Sprintf("%s:%s/%s", host, remotePath, filename)
		} else {
			destination = fmt.Sprintf("%s:%s", host, filename)
		}

		// Send file to server using SCP
		cmd := exec.Command("scp",
			"-o", "StrictHostKeyChecking=no",
			"-o", "UserKnownHostsFile=/dev/null",
			tempFile.Name(), destination)
		output, err := cmd.CombinedOutput()

		// Clean up temporary file
		os.Remove(tempFile.Name())

		if err != nil {
			fmt.Printf(colorYellow+"[WARNING] Could not send log to server: %v\nOutput: %s\n"+colorReset, err, output)
		} else {
			fmt.Printf(colorGreen+"[INFO] Log sent to server: %s\n"+colorReset, destination)
		}
	}
}

// parseDmidecodeToMap преобразует вывод dmidecode в карту для JSON
func parseDmidecodeToMap(output string) map[string]interface{} {
	systemInfo := make(map[string]interface{})

	// Простой парсер, который группирует информацию по секциям
	var currentSection string
	sectionData := make(map[string]interface{})

	lines := strings.Split(output, "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		// Начало новой секции
		if strings.HasPrefix(line, "Handle") {
			// Сохраняем предыдущую секцию, если она существует
			if currentSection != "" && len(sectionData) > 0 {
				systemInfo[currentSection] = sectionData
				sectionData = make(map[string]interface{})
			}
			currentSection = line
			continue
		}

		// Если строка содержит двоеточие, это пара ключ-значение
		if colonIndex := strings.Index(line, ":"); colonIndex != -1 {
			key := strings.TrimSpace(line[:colonIndex])
			value := strings.TrimSpace(line[colonIndex+1:])
			sectionData[key] = value
		}
	}

	// Сохраняем последнюю секцию
	if currentSection != "" && len(sectionData) > 0 {
		systemInfo[currentSection] = sectionData
	}

	return systemInfo
}

// runCommand запускает команду и возвращает её вывод
func runCommand(name string, args ...string) (string, error) {
	cmd := exec.Command(name, args...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	err := cmd.Run()
	return strings.TrimSpace(out.String()), err
}

// runCommandNoOutput запускает команду без вывода результата
func runCommandNoOutput(name string, args ...string) error {
	cmd := exec.Command(name, args...)
	var dummy bytes.Buffer
	cmd.Stdout = &dummy
	cmd.Stderr = &dummy
	return cmd.Run()
}

// getInterfacesWithMAC получает список интерфейсов с указанным MAC-адресом
func getInterfacesWithMAC(targetMAC string) ([]string, error) {
	output, err := runCommand("ip", "-o", "link", "show")
	if err != nil {
		return nil, fmt.Errorf("Failed to get ip link show: %v", err)
	}
	re := regexp.MustCompile(`^\d+:\s+([^:]+):.*link/ether\s+([0-9a-f:]+)`)
	var interfaces []string
	scanner := bufio.NewScanner(strings.NewReader(output))
	for scanner.Scan() {
		line := scanner.Text()
		matches := re.FindStringSubmatch(line)
		if len(matches) == 3 {
			iface := matches[1]
			macFound := matches[2]
			if strings.ToLower(macFound) == strings.ToLower(targetMAC) {
				interfaces = append(interfaces, iface)
			}
		}
	}
	if len(interfaces) == 0 {
		return nil, fmt.Errorf("No interface found with MAC address: %s", targetMAC)
	}
	return interfaces, nil
}

// writeMAcWithRetries пытается записать MAC-адрес с повторными попытками и пересборкой драйвера при необходимости
func writeMAcWithRetries(macInput string) error {
	targetMAC := strings.ToLower(macInput)
	// Если указанный MAC уже присутствует, пропускаем прошивку
	if ifaces, err := getInterfacesWithMAC(targetMAC); err == nil && len(ifaces) > 0 {
		fmt.Printf(colorGreen+"[INFO] MAC address %s already present on interface(s): %s. Skipping flashing.\n"+colorReset,
			targetMAC, strings.Join(ifaces, ", "))
		return nil
	}

	out, err := runCommand("uname", "-m")
	if err != nil {
		return fmt.Errorf("Failed to get machine architecture: %v", err)
	}
	arch := strings.TrimSpace(out)
	rtnic := filepath.Join(cDir, "rtnicpg", "rtnicpg-"+arch)

	oldIface, oldIP, err := getActiveInterfaceAndIP()
	if err != nil {
		fmt.Printf(colorYellow+"[WARNING] %v"+colorReset, err)
	} else {
		fmt.Printf("Old IP address for interface %s: %s\n", oldIface, oldIP)
	}

	// Первая попытка загрузить драйвер как есть
	driverErr := loadDriver()

	// Если загрузка драйвера не удалась, пытаемся пересобрать и загрузить снова
	if driverErr != nil {
		fmt.Printf(colorYellow+"[WARNING] Initial driver load failed: %v\nAttempting to recompile driver..."+colorReset+"\n", driverErr)

		// Пытаемся пересобрать драйвер
		rtnicpgPath := filepath.Join(cDir, "rtnicpg")
		if info, err := os.Stat(rtnicpgPath); err == nil && info.IsDir() {
			if err := runCommandNoOutput("make", "-C", rtnicpgPath, "clean", "all"); err != nil {
				criticalError("Failed to recompile driver: " + err.Error())
				return err
			}
			fmt.Println(colorGreen + "[INFO] Driver recompilation successful." + colorReset)

			// Пытаемся загрузить драйвер снова после пересборки
			if driverErr = loadDriver(); driverErr != nil {
				criticalError("Failed to load driver even after recompilation: " + driverErr.Error())
				return driverErr
			}
		} else {
			criticalError("rtnicpg directory does not exist, cannot recompile driver")
			return fmt.Errorf("rtnicpg directory does not exist, cannot recompile driver")
		}
	}

	if err := os.Chmod(rtnic, 0755); err != nil {
		return fmt.Errorf("Failed to chmod %s: %v", rtnic, err)
	}

	// Модифицируем MAC-адрес для команды (удаляем двоеточия)
	modmac := strings.ReplaceAll(macInput, ":", "")
	fmt.Println("Modified MAC for flashing:", modmac)

	// Пытаемся записать MAC с повторными попытками
	var macWriteSuccess bool = false
	var macWriteErr error

	for attempt := 1; attempt <= maxRetries; attempt++ {
		macWriteErr = runCommandNoOutput(rtnic, "/efuse", "/nicmac", "/nodeid", modmac)

		if macWriteErr == nil {
			fmt.Println(colorGreen + "[INFO] MAC address was successfully written, verifying..." + colorReset)
			macWriteSuccess = true
			break
		} else {
			fmt.Printf(colorYellow+"[WARNING] Attempt %d: Failed to write MAC: %v\n"+colorReset, attempt, macWriteErr)

			if attempt == 1 {
				// При первой неудаче пытаемся пересобрать драйвер
				fmt.Println(colorYellow + "[WARNING] MAC write failed. Attempting to recompile driver and try again..." + colorReset)
				rtnicpgPath := filepath.Join(cDir, "rtnicpg")
				if info, err := os.Stat(rtnicpgPath); err == nil && info.IsDir() {
					if err := runCommandNoOutput("make", "-C", rtnicpgPath, "clean", "all"); err != nil {
						fmt.Printf(colorYellow+"[WARNING] Failed to recompile driver: %v\n"+colorReset, err)
					} else {
						fmt.Println(colorGreen + "[INFO] Driver recompilation successful." + colorReset)
						if err := loadDriver(); err != nil {
							fmt.Printf(colorYellow+"[WARNING] Failed to reload driver after recompilation: %v\n"+colorReset, err)
						}
					}
				}
			}

			time.Sleep(1 * time.Second) // Более длительная задержка для аппаратных операций
		}
	}

	if !macWriteSuccess {
		criticalError("Failed to write MAC address after " + fmt.Sprintf("%d", maxRetries) + " attempts: " + macWriteErr.Error())
		return fmt.Errorf("Failed to write MAC address after %d attempts: %v", maxRetries, macWriteErr)
	}

	_ = runCommandNoOutput("rmmod", "pgdrv")
	if rtDrv != "" {
		if err := runCommandNoOutput("modprobe", rtDrv); err != nil {
			fmt.Printf(colorYellow+"[WARNING] Failed to modprobe %s: %v\n"+colorReset, rtDrv, err)
		}
	}

	// Проверяем, появились ли интерфейсы с установленным MAC
	ifaces, err := getInterfacesWithMAC(targetMAC)
	if err != nil {
		return fmt.Errorf("Failed to find interface with target MAC: %v", err)
	}
	fmt.Printf("Found interfaces with MAC %s: %v\n", targetMAC, ifaces)

	// Восстанавливаем сетевые настройки
	var newIface string
	if oldIface != "" {
		for _, iface := range ifaces {
			if iface == oldIface {
				newIface = iface
				break
			}
		}
	}
	if newIface == "" {
		newIface = ifaces[0]
		if len(ifaces) > 1 {
			fmt.Printf(colorYellow+"[WARNING] Multiple interfaces with matching MAC found. Using %s\n"+colorReset, newIface)
		}
	}

	if newIface != "" && oldIP != "" {
		maxRetries := 3
		var assignErr error
		for attempt := 1; attempt <= maxRetries; attempt++ {
			fmt.Printf("[INFO] Attempt %d: Restarting interface %s with IP %s\n", attempt, newIface, oldIP)

			// Выключаем интерфейс
			_ = runCommandNoOutput("ip", "link", "set", "dev", newIface, "down")

			// Удаляем все IP-адреса с интерфейса
			_ = runCommandNoOutput("ip", "addr", "flush", "dev", newIface)

			// Устанавливаем MAC-адрес
			_ = runCommandNoOutput("ip", "link", "set", "dev", newIface, "address", targetMAC)

			// Включаем интерфейс
			_ = runCommandNoOutput("ip", "link", "set", "dev", newIface, "up")

			// Назначаем только оригинальный IP
			assignErr = runCommandNoOutput("ip", "addr", "add", oldIP, "dev", newIface)

			if assignErr == nil {
				fmt.Printf(colorGreen+"[INFO] Interface %s restarted with IP %s\n"+colorReset, newIface, oldIP)
				break
			} else {
				fmt.Printf(colorYellow+"[WARNING] Attempt %d: Failed to assign IP %s to interface %s: %v\n"+colorReset, attempt, oldIP, newIface, assignErr)

				// Проверяем, не был ли уже назначен этот IP
				ipCheckOutput, _ := runCommand("ip", "addr", "show", "dev", newIface)
				if strings.Contains(ipCheckOutput, oldIP) {
					fmt.Printf(colorGreen+"[INFO] IP %s is already assigned to %s, continuing...\n"+colorReset, oldIP, newIface)
					assignErr = nil
					break
				}

				time.Sleep(500 * time.Millisecond) // Небольшая задержка между попытками
			}
		}
	} else {
		fmt.Println(colorYellow + "[WARNING] Could not find interface for " + targetMAC + " or no previous IP was stored." + colorReset)
	}

	return nil
}

// getActiveInterfaceAndIP получает активный интерфейс и его IP-адрес
func getActiveInterfaceAndIP() (string, string, error) {
	output, err := runCommand("ip", "a")
	if err != nil {
		return "", "", fmt.Errorf("Failed to get 'ip a' output: %v", err)
	}

	lines := strings.Split(output, "\n")
	var currentIface, currentIP string
	headerRe := regexp.MustCompile(`^\d+:\s+([^:]+):\s+<([^>]+)>`)
	for i, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if matches := headerRe.FindStringSubmatch(line); len(matches) == 3 {
			ifaceName := matches[1]
			flags := matches[2]
			if ifaceName == "lo" {
				continue
			}
			if !strings.Contains(flags, "UP") {
				continue
			}
			currentIface = ifaceName
			for j := i + 1; j < len(lines); j++ {
				nextLine := strings.TrimSpace(lines[j])
				if nextLine == "" {
					continue
				}
				if headerRe.MatchString(nextLine) {
					break
				}
				if strings.HasPrefix(nextLine, "inet ") {
					fields := strings.Fields(nextLine)
					if len(fields) >= 2 {
						currentIP = fields[1]
						break
					}
				}
			}
			if currentIP != "" {
				break
			}
		}
	}

	if currentIface == "" {
		return "", "", errors.New("no active interface found")
	}
	if currentIP == "" {
		return currentIface, "", errors.New("active interface found but no IPv4 address detected")
	}
	return currentIface, currentIP, nil
}

// loadDriver загружает необходимый драйвер
func loadDriver() error {
	moduleDefault := "pgdrv"
	modulesToRemove := []string{"r8169", "r8168", "r8125", "r8101"}

	rtnicpgPath := filepath.Join(cDir, "rtnicpg")
	if info, err := os.Stat(rtnicpgPath); err != nil || !info.IsDir() {
		return fmt.Errorf("Directory %s does not exist", rtnicpgPath)
	}

	for _, mod := range modulesToRemove {
		if isModuleLoaded(mod) {
			fmt.Printf("Removing module: %s\n", mod)
			if err := runCommandNoOutput("rmmod", mod); err != nil {
				fmt.Printf("[WARNING] Could not remove module %s: %v\n", mod, err)
			} else {
				fmt.Printf("[INFO] Module %s successfully removed.\n", mod)
				rtDrv = mod
			}
		}
	}

	var targetModule string
	// Получаем версию ядра для включения в имя файла драйвера
	kernelVersion, err := runCommand("uname", "-r")
	if err != nil {
		kernelVersion = "unknown"
	} else {
		kernelVersion = strings.TrimSpace(kernelVersion)
	}
	if rtDrv != "" {
		targetModule = rtDrv + "_mod_" + kernelVersion + ".ko"
	} else {
		targetModule = moduleDefault + ".ko"
	}
	targetModulePath := filepath.Join(rtnicpgPath, targetModule)

	// Проверка, существует ли драйвер и загружен ли он
	if _, err := os.Stat(targetModulePath); err == nil {
		fmt.Printf("[INFO] Found existing driver file %s. Loading it...\n", targetModulePath)
		modName := strings.TrimSuffix(targetModule, ".ko")
		if isModuleLoaded(modName) {
			fmt.Printf("[INFO] Module %s is already loaded.\n", modName)
			return nil
		}
		if err := runCommandNoOutput("insmod", targetModulePath); err != nil {
			return fmt.Errorf("Failed to load module %s: %v", targetModulePath, err)
		}
		fmt.Printf("[INFO] Module %s loaded successfully.\n", targetModule)
		return nil
	}

	// Если драйвер не существует, компилируем его
	fmt.Printf("[INFO] Compiling module %s.\n", moduleDefault)
	if err := runCommandNoOutput("make", "-C", rtnicpgPath, "clean", "all"); err != nil {
		return fmt.Errorf("Compilation failed: %v", err)
	}
	fmt.Println("[INFO] Compilation completed successfully.")

	builtModule := filepath.Join(rtnicpgPath, moduleDefault+".ko")
	if _, err := os.Stat(builtModule); errors.Is(err, fs.ErrNotExist) {
		return fmt.Errorf("Compiled module %s not found", builtModule)
	}

	// Переименовываем модуль при необходимости
	if rtDrv != "" {
		err := os.Rename(builtModule, targetModulePath)
		if err != nil {
			return fmt.Errorf("Failed to rename %s to %s: %v", builtModule, targetModulePath, err)
		}
	} else {
		targetModulePath = builtModule
	}

	// Загружаем новый скомпилированный модуль
	if err := runCommandNoOutput("insmod", targetModulePath); err != nil {
		return fmt.Errorf("Failed to load module %s: %v", targetModulePath, err)
	}
	fmt.Printf("[INFO] Module %s loaded successfully.\n", targetModulePath)
	return nil
}

// isModuleLoaded проверяет, загружен ли модуль ядра
func isModuleLoaded(mod string) bool {
	out, err := runCommand("lsmod")
	if err != nil {
		return false
	}
	lines := strings.Split(out, "\n")
	for _, line := range lines {
		fields := strings.Fields(line)
		if len(fields) > 0 && fields[0] == mod {
			return true
		}
	}
	return false
}
