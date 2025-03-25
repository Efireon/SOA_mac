package main

import (
	"bufio"
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
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
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
	fileVersion     = 1              // Версия формата файла
)

// ANSI escape sequences для цветного вывода
const (
	colorReset  = "\033[0m"
	colorRed    = "\033[31m"
	colorGreen  = "\033[32m"
	colorYellow = "\033[33m"
	colorBlue   = "\033[34m"
	colorCyan   = "\033[36m"
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

// RecentPool хранит информацию о недавно использованных пулах
type RecentPool struct {
	Path        string    `json:"path"`
	LastOpened  time.Time `json:"last_opened"`
	Description string    `json:"description,omitempty"`
}

// Config хранит настройки программы
type Config struct {
	RecentPools         []RecentPool `json:"recent_pools"`
	DefaultVendorPrefix string       `json:"default_vendor_prefix,omitempty"`
	LastDirectory       string       `json:"last_directory,omitempty"`
	MaxRecentPools      int          `json:"max_recent_pools"`
}

// Глобальная конфигурация
var appConfig Config

// Константы для конфигурации
const (
	configFileName = ".mac_pool_manager.json"
	maxRecentPools = 10
)

func main() {
	// Определение флагов командной строки
	poolFilePtr := flag.String("file", "", "Path to MAC address pool file")
	vendorPrefixPtr := flag.String("prefix", "", "Vendor prefix for MAC addresses (e.g., '00:1A:2B')")
	flag.Parse()

	// Загрузка конфигурации
	loadConfig()

	// Получение начального пути к пулу
	var currentPoolPath string
	if *poolFilePtr != "" {
		currentPoolPath = *poolFilePtr
	}

	// Получение префикса производителя
	vendorPrefix := *vendorPrefixPtr
	if vendorPrefix == "" {
		vendorPrefix = appConfig.DefaultVendorPrefix
	}

	// Проверка и стандартизация префикса производителя, если указан
	if vendorPrefix != "" {
		if !isVendorPrefixValid(vendorPrefix) {
			fmt.Println(colorRed + "Warning: Invalid vendor prefix format. Should be like '00:1A:2B'." + colorReset)
			vendorPrefix = ""
		} else {
			// Стандартизируем формат
			vendorPrefix = strings.ToUpper(vendorPrefix)
		}
	}

	// Приветствие
	clearScreen()
	showWelcomeScreen()

	// Если путь к пулу не указан, переходим в меню выбора пула
	if currentPoolPath == "" {
		currentPoolPath = selectPoolFile()
	}

	// Проверка существования выбранного пула
	poolExists := false
	if currentPoolPath != "" {
		if _, err := os.Stat(currentPoolPath); err == nil {
			poolExists = true
			addToRecentPools(currentPoolPath)
		}
	}

	// Основной рабочий цикл
	for {
		clearScreen()
		showHeader()

		// Отображение текущего пула
		if currentPoolPath != "" {
			if poolExists {
				fmt.Println("Current Pool File:", colorCyan+currentPoolPath+colorReset)
			} else {
				fmt.Println("Current Pool File:", colorYellow+currentPoolPath+colorReset, "(Not created yet)")
			}
		} else {
			fmt.Println("No pool file selected")
		}

		// Главное меню
		fmt.Println("\nOptions:")
		fmt.Println("P. Select different pool file")
		fmt.Println("N. Create new MAC address pool")

		if poolExists {
			fmt.Println("\nPool Operations:")
			fmt.Println("1. Add MAC addresses to pool")
			fmt.Println("2. Remove MAC addresses from pool")
			fmt.Println("3. List MAC addresses in pool")
			fmt.Println("4. Reset MAC address status (mark as unused)")
			fmt.Println("5. Change encryption password")
			fmt.Println("6. Export pool statistics")
			fmt.Println("7. View pool information")
		}

		fmt.Println("\nS. Settings")
		fmt.Println("Q. Exit")

		// Получение выбора пользователя
		var choice string
		fmt.Print("\nSelect option: ")
		reader := bufio.NewReader(os.Stdin)
		choice, _ = reader.ReadString('\n')
		choice = strings.TrimSpace(choice)
		choice = strings.ToUpper(choice)

		switch choice {
		case "Q":
			fmt.Println("Saving configuration and exiting...")
			saveConfig()
			return

		case "P":
			// Выбор другого пула
			newPath := selectPoolFile()
			if newPath != "" {
				currentPoolPath = newPath
				poolExists = false
				if _, err := os.Stat(currentPoolPath); err == nil {
					poolExists = true
					addToRecentPools(currentPoolPath)
				}
			}

		case "N":
			// Создание нового пула с указанием пути
			newPath := promptForNewPoolPath()
			if newPath != "" {
				err := createNewPool(newPath, vendorPrefix)
				if err == nil {
					currentPoolPath = newPath
					poolExists = true
					addToRecentPools(currentPoolPath)

					// Спросим пользователя, хочет ли он сразу добавить MAC-адреса
					reader := bufio.NewReader(os.Stdin)
					fmt.Print("\nWould you like to add MAC addresses to the pool now? (yes/no): ")
					choice, _ := reader.ReadString('\n')
					choice = strings.TrimSpace(choice)
					if strings.ToLower(choice) == "yes" {
						addMACsToPool(currentPoolPath)
					}
				}
			}

		case "1":
			if poolExists {
				addMACsToPool(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "2":
			if poolExists {
				removeMACsFromPool(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "3":
			if poolExists {
				listMACsInPool(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "4":
			if poolExists {
				resetMACStatus(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "5":
			if poolExists {
				changePassword(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "6":
			if poolExists {
				exportPoolStats(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "7":
			if poolExists {
				viewPoolInfo(currentPoolPath)
			} else {
				showNoPoolError()
			}

		case "S":
			vendorPrefix = showSettingsMenu(vendorPrefix)

		default:
			fmt.Println(colorRed + "Invalid option, please try again." + colorReset)
			time.Sleep(1 * time.Second)
		}
	}
}

// clearScreen очищает экран терминала
func clearScreen() {
	// Для Unix-подобных систем
	cmd := exec.Command("clear")
	cmd.Stdout = os.Stdout
	cmd.Run()

	// Для Windows
	cmd = exec.Command("cmd", "/c", "cls")
	cmd.Stdout = os.Stdout
	cmd.Run()
}

// showHeader выводит заголовок программы
func showHeader() {
	fmt.Println(colorBlue + "╔══════════════════════════════════════════╗" + colorReset)
	fmt.Println(colorBlue + "║           MAC Address Pool Manager       ║" + colorReset)
	fmt.Println(colorBlue + "╚══════════════════════════════════════════╝" + colorReset)
	fmt.Println()
}

// showWelcomeScreen выводит приветственный экран
func showWelcomeScreen() {
	showHeader()
	fmt.Println("Welcome to MAC Address Pool Manager!")
	fmt.Println("This tool allows you to create and manage MAC address pools.")
	fmt.Println("The pools will be encrypted and can only be used by MAC Flasher.")
	fmt.Println()
	fmt.Println("Press ENTER to continue...")
	bufio.NewReader(os.Stdin).ReadString('\n')
}

// selectPoolFile показывает меню выбора файла пула
func selectPoolFile() string {
	for {
		clearScreen()
		showHeader()
		fmt.Println("Select MAC Address Pool:")
		fmt.Println()

		// Отображение недавно использованных пулов
		if len(appConfig.RecentPools) > 0 {
			fmt.Println(colorGreen + "Recent Pools:" + colorReset)
			for i, pool := range appConfig.RecentPools {
				fmt.Printf("%d. %s", i+1, pool.Path)
				if pool.Description != "" {
					fmt.Printf(" (%s)", pool.Description)
				}
				fmt.Printf(" - Last opened: %s\n", pool.LastOpened.Format("2006-01-02 15:04:05"))
			}
			fmt.Println()
		}

		// Опции меню
		fmt.Println("Options:")
		fmt.Println("C. Create new pool file")
		fmt.Println("B. Browse for existing pool file")
		fmt.Println("S. Search in current directory")
		fmt.Println("N. Enter pool file path")
		fmt.Println("R. Return to main menu")

		fmt.Print("\nSelect option: ")
		reader := bufio.NewReader(os.Stdin)
		choice, _ := reader.ReadString('\n')
		choice = strings.TrimSpace(choice)
		choice = strings.ToUpper(choice)

		// Проверка выбора числовой опции (недавние пулы)
		if num, err := strconv.Atoi(choice); err == nil && num > 0 && num <= len(appConfig.RecentPools) {
			return appConfig.RecentPools[num-1].Path
		}

		switch choice {
		case "C":
			// Создание нового пула
			path := promptForNewPoolPath()
			if path != "" {
				// Создаем новый пул непосредственно здесь
				vendorPrefix := appConfig.DefaultVendorPrefix
				if err := createNewPool(path, vendorPrefix); err == nil {
					return path // Возвращаем путь к новому пулу
				}
			}

		case "B":
			// Просмотр файлов в директориях
			path := browseForPoolFile()
			if path != "" {
				return path
			}

		case "S":
			// Поиск .enc файлов в текущей директории
			path := searchEncFilesInCurrentDir()
			if path != "" {
				return path
			}

		case "N":
			// Ввод нового пути
			fmt.Print("Enter path to pool file: ")
			path, _ := reader.ReadString('\n')
			path = strings.TrimSpace(path)
			if path != "" {
				// Если путь относительный, добавляем текущую директорию
				if !filepath.IsAbs(path) {
					currDir, _ := os.Getwd()
					path = filepath.Join(currDir, path)
				}
				return path
			}

		case "R":
			return ""

		default:
			fmt.Println(colorRed + "Invalid option, please try again." + colorReset)
			time.Sleep(1 * time.Second)
		}
	}
}

// browseForPoolFile позволяет просматривать файловую систему для выбора файла пула
func browseForPoolFile() string {
	currDir := appConfig.LastDirectory
	if currDir == "" {
		var err error
		currDir, err = os.Getwd()
		if err != nil {
			fmt.Println(colorRed+"Error getting current directory:"+colorReset, err)
			time.Sleep(2 * time.Second)
			return ""
		}
	}

	for {
		clearScreen()
		showHeader()
		fmt.Printf("Current directory: %s\n\n", currDir)

		// Чтение содержимого директории
		files, err := os.ReadDir(currDir)
		if err != nil {
			fmt.Println(colorRed+"Error reading directory:"+colorReset, err)
			time.Sleep(2 * time.Second)
			return ""
		}

		// Сначала выводим директории
		fmt.Println(colorBlue + "Directories:" + colorReset)
		dirsCount := 0
		for i, file := range files {
			if file.IsDir() {
				fmt.Printf("%d. %s/\n", i+1, file.Name())
				dirsCount++
			}
		}

		if dirsCount == 0 {
			fmt.Println("  No subdirectories")
		}

		// Затем .enc файлы
		fmt.Println("\n" + colorGreen + "Pool Files (.enc):" + colorReset)
		encCount := 0
		for i, file := range files {
			if !file.IsDir() && strings.HasSuffix(strings.ToLower(file.Name()), ".enc") {
				fmt.Printf("%d. %s\n", i+1, file.Name())
				encCount++
			}
		}

		if encCount == 0 {
			fmt.Println("  No .enc files found")
		}

		fmt.Println("\nOptions:")
		fmt.Println("U. Go up one directory")
		fmt.Println("R. Return to previous menu")

		fmt.Print("\nSelect option (number for file/directory): ")
		reader := bufio.NewReader(os.Stdin)
		choice, _ := reader.ReadString('\n')
		choice = strings.TrimSpace(choice)
		choice = strings.ToUpper(choice)

		if choice == "U" {
			// Переход на уровень выше
			parentDir := filepath.Dir(currDir)
			if parentDir != currDir {
				currDir = parentDir
				appConfig.LastDirectory = currDir
			} else {
				fmt.Println(colorYellow + "Already at root directory" + colorReset)
				time.Sleep(1 * time.Second)
			}
		} else if choice == "R" {
			return ""
		} else if num, err := strconv.Atoi(choice); err == nil && num > 0 && num <= len(files) {
			// Выбор файла или директории
			selected := files[num-1]
			path := filepath.Join(currDir, selected.Name())

			if selected.IsDir() {
				// Переход в выбранную директорию
				currDir = path
				appConfig.LastDirectory = currDir
			} else if strings.HasSuffix(strings.ToLower(selected.Name()), ".enc") {
				// Выбор .enc файла
				return path
			} else {
				fmt.Println(colorYellow + "Please select a .enc file or a directory" + colorReset)
				time.Sleep(1 * time.Second)
			}
		} else {
			fmt.Println(colorRed + "Invalid option, please try again." + colorReset)
			time.Sleep(1 * time.Second)
		}
	}
}

// searchEncFilesInCurrentDir ищет все .enc файлы в текущей директории
func searchEncFilesInCurrentDir() string {
	currDir, err := os.Getwd()
	if err != nil {
		fmt.Println(colorRed+"Error getting current directory:"+colorReset, err)
		time.Sleep(2 * time.Second)
		return ""
	}

	clearScreen()
	showHeader()
	fmt.Printf("Searching for .enc files in: %s\n\n", currDir)

	// Поиск .enc файлов
	files, err := filepath.Glob(filepath.Join(currDir, "*.enc"))
	if err != nil {
		fmt.Println(colorRed+"Error searching for files:"+colorReset, err)
		time.Sleep(2 * time.Second)
		return ""
	}

	if len(files) == 0 {
		fmt.Println(colorYellow + "No .enc files found in the current directory." + colorReset)
		fmt.Println("Press ENTER to return...")
		bufio.NewReader(os.Stdin).ReadString('\n')
		return ""
	}

	// Отображение найденных файлов
	fmt.Println(colorGreen + "Found .enc files:" + colorReset)
	for i, file := range files {
		// Получение информации о файле
		fileInfo, err := os.Stat(file)
		if err != nil {
			continue
		}

		fileName := filepath.Base(file)
		modTime := fileInfo.ModTime().Format("2006-01-02 15:04:05")
		fileSize := byteCountSI(fileInfo.Size())

		fmt.Printf("%d. %s (Size: %s, Modified: %s)\n", i+1, fileName, fileSize, modTime)
	}

	fmt.Println("\nR. Return to previous menu")

	fmt.Print("\nSelect file: ")
	reader := bufio.NewReader(os.Stdin)
	choice, _ := reader.ReadString('\n')
	choice = strings.TrimSpace(choice)
	choice = strings.ToUpper(choice)

	if choice == "R" {
		return ""
	} else if num, err := strconv.Atoi(choice); err == nil && num > 0 && num <= len(files) {
		// Возвращаем выбранный файл
		return files[num-1]
	} else {
		fmt.Println(colorRed + "Invalid option, please try again." + colorReset)
		time.Sleep(1 * time.Second)
		return ""
	}
}

// byteCountSI форматирует размер файла в читаемом виде
func byteCountSI(b int64) string {
	const unit = 1000
	if b < unit {
		return fmt.Sprintf("%d B", b)
	}
	div, exp := int64(unit), 0
	for n := b / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %cB", float64(b)/float64(div), "kMGTPE"[exp])
}

// promptForNewPoolPath запрашивает путь для нового пула
func promptForNewPoolPath() string {
	clearScreen()
	showHeader()
	fmt.Println("Create New MAC Address Pool")
	fmt.Println()

	// Получение текущей директории
	currDir, err := os.Getwd()
	if err != nil {
		fmt.Println(colorRed+"Error getting current directory:"+colorReset, err)
		time.Sleep(2 * time.Second)
		return ""
	}

	fmt.Printf("Current directory: %s\n\n", currDir)
	fmt.Println("1. Create in current directory")
	fmt.Println("2. Specify full path")
	fmt.Println("3. Return to previous menu")

	fmt.Print("\nSelect option: ")
	reader := bufio.NewReader(os.Stdin)
	choice, _ := reader.ReadString('\n')
	choice = strings.TrimSpace(choice)

	switch choice {
	case "1":
		// Создание в текущей директории
		fmt.Print("\nEnter filename (default: mac_pool.enc): ")
		filename, _ := reader.ReadString('\n')
		filename = strings.TrimSpace(filename)

		if filename == "" {
			filename = "mac_pool.enc"
		}

		// Добавляем расширение .enc, если не указано
		if !strings.HasSuffix(strings.ToLower(filename), ".enc") {
			filename += ".enc"
		}

		return filepath.Join(currDir, filename)

	case "2":
		// Указание полного пути
		fmt.Print("\nEnter full path to new pool file: ")
		path, _ := reader.ReadString('\n')
		path = strings.TrimSpace(path)

		if path == "" {
			return ""
		}

		// Добавляем расширение .enc, если не указано
		if !strings.HasSuffix(strings.ToLower(path), ".enc") {
			path += ".enc"
		}

		return path

	case "3":
		return ""

	default:
		fmt.Println(colorRed + "Invalid option, please try again." + colorReset)
		time.Sleep(1 * time.Second)
		return ""
	}
}

// showNoPoolError показывает сообщение о том, что пул не выбран или не существует
func showNoPoolError() {
	fmt.Println(colorYellow + "Please create or select a pool first" + colorReset)
	fmt.Println("Press ENTER to continue...")
	bufio.NewReader(os.Stdin).ReadString('\n')
}

// viewPoolInfo показывает информацию о пуле
func viewPoolInfo(poolFile string) error {
	// Загрузка пула
	pool, _, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		fmt.Println("Press ENTER to continue...")
		bufio.NewReader(os.Stdin).ReadString('\n')
		return err
	}

	clearScreen()
	showHeader()
	fmt.Printf("Pool Information: %s\n\n", poolFile)

	// Подсчет статистики
	unusedCount := 0
	usedCount := 0
	reservedCount := 0

	for _, addr := range pool.Addresses {
		if addr.Used {
			usedCount++
		} else if addr.Reserved {
			reservedCount++
		} else {
			unusedCount++
		}
	}

	// Отображение основной информации
	fmt.Printf("File: %s\n", poolFile)
	fmt.Printf("File size: %s\n", byteCountSI(getFileSize(poolFile)))
	fmt.Printf("Created by: %s\n", pool.CreatedBy)
	fmt.Printf("Last updated: %s\n", pool.LastUpdated.Format("2006-01-02 15:04:05"))
	fmt.Printf("Version: %d\n", pool.Version)

	if pool.MACVendorPrefix != "" {
		fmt.Printf("Vendor prefix: %s\n", pool.MACVendorPrefix)
	}

	fmt.Printf("\nTotal MAC addresses: %d\n", len(pool.Addresses))
	fmt.Printf("Used: %d (%.1f%%)\n", usedCount, percentage(usedCount, len(pool.Addresses)))
	fmt.Printf("Unused: %d (%.1f%%)\n", unusedCount, percentage(unusedCount, len(pool.Addresses)))
	fmt.Printf("Reserved: %d (%.1f%%)\n", reservedCount, percentage(reservedCount, len(pool.Addresses)))

	// Отображение последних использованных адресов
	if usedCount > 0 {
		fmt.Printf("\nRecently used MAC addresses:\n")

		// Сортируем адреса по времени использования (от новых к старым)
		var usedAddrs []MACAddress
		for _, addr := range pool.Addresses {
			if addr.Used {
				usedAddrs = append(usedAddrs, addr)
			}
		}

		sort.Slice(usedAddrs, func(i, j int) bool {
			return usedAddrs[i].UsedAt.After(usedAddrs[j].UsedAt)
		})

		// Отображаем максимум 5 последних адресов
		limit := 5
		if len(usedAddrs) < limit {
			limit = len(usedAddrs)
		}

		for i := 0; i < limit; i++ {
			addr := usedAddrs[i]
			fmt.Printf("  %s - Used at %s", addr.Address, addr.UsedAt.Format("2006-01-02 15:04:05"))
			if addr.UsedBy != "" {
				fmt.Printf(" by %s", addr.UsedBy)
			}
			fmt.Println()
		}
	}

	fmt.Println("\nPress ENTER to return...")
	bufio.NewReader(os.Stdin).ReadString('\n')
	return nil
}

// getFileSize возвращает размер файла
func getFileSize(path string) int64 {
	fileInfo, err := os.Stat(path)
	if err != nil {
		return 0
	}
	return fileInfo.Size()
}

// percentage вычисляет процент от общего значения
func percentage(part, total int) float64 {
	if total == 0 {
		return 0.0
	}
	return float64(part) / float64(total) * 100.0
}

// showSettingsMenu показывает меню настроек
func showSettingsMenu(currentVendorPrefix string) string {
	clearScreen()
	showHeader()
	fmt.Println("Settings")
	fmt.Println()

	fmt.Printf("1. Default vendor prefix: %s\n", currentVendorPrefix)
	fmt.Printf("2. Maximum recent pools: %d\n", appConfig.MaxRecentPools)
	fmt.Println("3. Clear recent pools list")
	fmt.Println("4. Save and exit settings")

	fmt.Print("\nSelect option: ")
	reader := bufio.NewReader(os.Stdin)
	choice, _ := reader.ReadString('\n')
	choice = strings.TrimSpace(choice)

	switch choice {
	case "1":
		// Изменение префикса производителя
		fmt.Printf("\nCurrent default vendor prefix: %s\n", currentVendorPrefix)
		fmt.Print("Enter new vendor prefix (e.g., 00:1A:2B): ")
		prefix, _ := reader.ReadString('\n')
		prefix = strings.TrimSpace(prefix)

		if prefix == "" {
			return currentVendorPrefix
		}

		if !isVendorPrefixValid(prefix) {
			fmt.Println(colorRed + "Invalid vendor prefix format. Should be like '00:1A:2B'. Setting not changed." + colorReset)
			time.Sleep(2 * time.Second)
			return currentVendorPrefix
		}

		// Стандартизируем формат
		prefix = strings.ToUpper(prefix)
		appConfig.DefaultVendorPrefix = prefix
		saveConfig()

		fmt.Println(colorGreen + "Default vendor prefix updated successfully." + colorReset)
		time.Sleep(1 * time.Second)
		return prefix

	case "2":
		// Изменение максимального количества недавних пулов
		fmt.Printf("\nCurrent maximum recent pools: %d\n", appConfig.MaxRecentPools)
		fmt.Print("Enter new value (1-20): ")
		maxStr, _ := reader.ReadString('\n')
		maxStr = strings.TrimSpace(maxStr)

		max, err := strconv.Atoi(maxStr)
		if err != nil || max < 1 || max > 20 {
			fmt.Println(colorRed + "Invalid value. Please enter a number between 1 and 20. Setting not changed." + colorReset)
			time.Sleep(2 * time.Second)
			return currentVendorPrefix
		}

		appConfig.MaxRecentPools = max

		// Обрезаем список недавних пулов, если он стал длиннее максимума
		if len(appConfig.RecentPools) > max {
			appConfig.RecentPools = appConfig.RecentPools[:max]
		}

		saveConfig()

		fmt.Println(colorGreen + "Maximum recent pools updated successfully." + colorReset)
		time.Sleep(1 * time.Second)
		return currentVendorPrefix

	case "3":
		// Очистка списка недавних пулов
		fmt.Print("\nAre you sure you want to clear the recent pools list? (yes/no): ")
		confirm, _ := reader.ReadString('\n')
		confirm = strings.TrimSpace(confirm)

		if strings.ToLower(confirm) == "yes" {
			appConfig.RecentPools = []RecentPool{}
			saveConfig()
			fmt.Println(colorGreen + "Recent pools list cleared successfully." + colorReset)
			time.Sleep(1 * time.Second)
		}
		return currentVendorPrefix

	case "4":
		return currentVendorPrefix

	default:
		fmt.Println(colorRed + "Invalid option, please try again." + colorReset)
		time.Sleep(1 * time.Second)
		return currentVendorPrefix
	}
}

// addToRecentPools добавляет путь к пулу в список недавно использованных
func addToRecentPools(path string) {
	// Проверяем, есть ли уже такой путь в списке
	for i, pool := range appConfig.RecentPools {
		if pool.Path == path {
			// Обновляем время последнего открытия
			appConfig.RecentPools[i].LastOpened = time.Now()

			// Перемещаем на первую позицию
			if i > 0 {
				appConfig.RecentPools = append(appConfig.RecentPools[:i], appConfig.RecentPools[i+1:]...)
				appConfig.RecentPools = append([]RecentPool{
					{
						Path:        path,
						LastOpened:  time.Now(),
						Description: appConfig.RecentPools[i].Description,
					},
				}, appConfig.RecentPools...)
			}

			saveConfig()
			return
		}
	}

	// Добавляем новый путь в начало списка
	appConfig.RecentPools = append([]RecentPool{
		{
			Path:       path,
			LastOpened: time.Now(),
		},
	}, appConfig.RecentPools...)

	// Ограничиваем количество недавних пулов
	maxRecent := appConfig.MaxRecentPools
	if maxRecent <= 0 {
		maxRecent = maxRecentPools
	}

	if len(appConfig.RecentPools) > maxRecent {
		appConfig.RecentPools = appConfig.RecentPools[:maxRecent]
	}

	saveConfig()
}

// loadConfig загружает конфигурацию из файла
func loadConfig() {
	// Путь к файлу конфигурации в домашней директории пользователя
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return
	}

	configPath := filepath.Join(homeDir, configFileName)

	// Проверка наличия файла
	if _, err := os.Stat(configPath); os.IsNotExist(err) {
		// Файл не существует, создаем конфигурацию по умолчанию
		appConfig = Config{
			RecentPools:    []RecentPool{},
			MaxRecentPools: maxRecentPools,
		}
		return
	}

	// Чтение и разбор файла конфигурации
	data, err := os.ReadFile(configPath)
	if err != nil {
		return
	}

	if err := json.Unmarshal(data, &appConfig); err != nil {
		// В случае ошибки используем конфигурацию по умолчанию
		appConfig = Config{
			RecentPools:    []RecentPool{},
			MaxRecentPools: maxRecentPools,
		}
		return
	}

	// Устанавливаем значение по умолчанию, если не указано
	if appConfig.MaxRecentPools <= 0 {
		appConfig.MaxRecentPools = maxRecentPools
	}
}

// saveConfig сохраняет конфигурацию в файл
func saveConfig() {
	// Путь к файлу конфигурации в домашней директории пользователя
	homeDir, err := os.UserHomeDir()
	if err != nil {
		return
	}

	configPath := filepath.Join(homeDir, configFileName)

	// Преобразование в JSON
	data, err := json.MarshalIndent(appConfig, "", "  ")
	if err != nil {
		return
	}

	// Сохранение в файл
	os.WriteFile(configPath, data, 0600)
}

// createNewPool создает новый пул MAC-адресов
func createNewPool(poolFile, vendorPrefix string) error {
	if _, err := os.Stat(poolFile); err == nil {
		fmt.Printf("MAC pool file %s already exists. Overwrite? (yes/no): ", poolFile)
		var confirm string
		fmt.Scanln(&confirm)
		if strings.ToLower(confirm) != "yes" {
			fmt.Println("Operation cancelled.")
			return errors.New("operation cancelled")
		}
	}

	// Запрос пароля
	fmt.Print("Set encryption password: ")
	password, err := term.ReadPassword(int(syscall.Stdin))
	fmt.Println()
	if err != nil {
		fmt.Println(colorRed+"Failed to read password:"+colorReset, err)
		return err
	}

	// Подтверждение пароля
	fmt.Print("Confirm password: ")
	confirmPassword, err := term.ReadPassword(int(syscall.Stdin))
	fmt.Println()
	if err != nil {
		fmt.Println(colorRed+"Failed to read password:"+colorReset, err)
		return err
	}

	if string(password) != string(confirmPassword) {
		fmt.Println(colorRed + "Passwords do not match!" + colorReset)
		return errors.New("passwords do not match")
	}

	if len(password) < 8 {
		fmt.Println(colorRed + "Password must be at least 8 characters long!" + colorReset)
		return errors.New("password too short")
	}

	// Получение имени пользователя
	hostname, _ := os.Hostname()
	username := os.Getenv("USER")
	if username == "" {
		username = "unknown"
	}
	creator := fmt.Sprintf("%s@%s", username, hostname)

	// Создание пустого пула
	pool := MACPool{
		Version:     fileVersion,
		Addresses:   []MACAddress{},
		LastUpdated: time.Now(),
		CreatedBy:   creator,
	}

	if vendorPrefix != "" {
		pool.MACVendorPrefix = vendorPrefix
		fmt.Printf(colorGreen+"Using vendor prefix: %s\n"+colorReset, vendorPrefix)
	}

	// Добавление HMAC подписи
	signPool(&pool, string(password))

	// Шифрование и сохранение
	err = saveEncryptedPool(pool, string(password), poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to save pool:"+colorReset, err)
		return err
	}

	fmt.Println(colorGreen + "MAC address pool created successfully!" + colorReset)

	// Спросим пользователя, хочет ли он сразу добавить MAC-адреса
	fmt.Print("Would you like to add MAC addresses to the pool now? (yes/no): ")
	var addMacs string
	fmt.Scanln(&addMacs)
	if strings.ToLower(addMacs) == "yes" {
		return addMACsToPool(poolFile)
	}

	return nil
}

// addMACsToPool добавляет MAC-адреса в пул
func addMACsToPool(poolFile string) error {
	// Загрузка существующего пула
	pool, password, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		return err
	}

	// Предложить варианты добавления
	fmt.Println("\nHow would you like to add MAC addresses?")
	fmt.Println("1. Enter MAC addresses manually (one per line)")
	fmt.Println("2. Generate MAC addresses with vendor prefix")
	fmt.Println("3. Import from file")
	fmt.Println("0. Cancel")

	var choice string
	fmt.Print("\nSelect option: ")
	fmt.Scanln(&choice)

	var newMACs []string

	switch choice {
	case "0":
		fmt.Println("Operation cancelled.")
		return nil
	case "1":
		// Ручной ввод
		fmt.Println("Enter MAC addresses (one per line, empty line to finish):")
		scanner := bufio.NewScanner(os.Stdin)
		for {
			fmt.Print("> ")
			scanner.Scan()
			input := strings.TrimSpace(scanner.Text())
			if input == "" {
				break
			}

			// Проверка формата MAC
			if !isMACValid(input) {
				fmt.Printf(colorYellow+"Invalid MAC format: %s (skipped)\n"+colorReset, input)
				continue
			}

			// Стандартизация формата
			mac := standardizeMACFormat(input)

			// Проверка на дубликаты в вводе
			isDuplicate := false
			for _, m := range newMACs {
				if strings.EqualFold(m, mac) {
					fmt.Printf(colorYellow+"Duplicate MAC in your input: %s (skipped)\n"+colorReset, mac)
					isDuplicate = true
					break
				}
			}

			if !isDuplicate {
				// Проверка на дубликаты в существующем пуле
				for _, addr := range pool.Addresses {
					if strings.EqualFold(addr.Address, mac) {
						fmt.Printf(colorYellow+"MAC %s already exists in pool (skipped)\n"+colorReset, mac)
						isDuplicate = true
						break
					}
				}
			}

			if !isDuplicate {
				newMACs = append(newMACs, mac)
			}
		}

	case "2":
		// Генерация
		vendorPrefix := pool.MACVendorPrefix
		if vendorPrefix == "" {
			fmt.Print("Enter vendor prefix (e.g., 00:1A:2B): ")
			fmt.Scanln(&vendorPrefix)
			if !isVendorPrefixValid(vendorPrefix) {
				fmt.Println(colorRed + "Invalid vendor prefix format." + colorReset)
				return errors.New("invalid vendor prefix")
			}
			vendorPrefix = strings.ToUpper(vendorPrefix)
		}

		fmt.Print("How many MAC addresses to generate: ")
		var count int
		fmt.Scanln(&count)
		if count <= 0 || count > 10000 {
			fmt.Println(colorRed + "Invalid count. Please enter a number between 1 and 10000." + colorReset)
			return errors.New("invalid count")
		}

		// Генерируем адреса
		generatedMACs, err := generateMACAddresses(vendorPrefix, count, pool.Addresses)
		if err != nil {
			fmt.Println(colorRed+"Error generating MAC addresses:"+colorReset, err)
			return err
		}
		newMACs = generatedMACs

	case "3":
		// Импорт из файла
		fmt.Print("Enter path to file: ")
		var filePath string
		fmt.Scanln(&filePath)

		data, err := os.ReadFile(filePath)
		if err != nil {
			fmt.Println(colorRed+"Error reading file:"+colorReset, err)
			return err
		}

		scanner := bufio.NewScanner(strings.NewReader(string(data)))
		for scanner.Scan() {
			line := strings.TrimSpace(scanner.Text())
			if line == "" || strings.HasPrefix(line, "#") {
				continue
			}

			// Извлекаем MAC из строки (в случае если в строке есть дополнительные данные)
			re := regexp.MustCompile(`([0-9A-Fa-f]{2}[:-]){5}[0-9A-Fa-f]{2}`)
			macMatches := re.FindAllString(line, -1)

			for _, mac := range macMatches {
				if !isMACValid(mac) {
					fmt.Printf(colorYellow+"Invalid MAC format: %s (skipped)\n"+colorReset, mac)
					continue
				}

				// Стандартизация формата
				mac = standardizeMACFormat(mac)

				// Проверка на дубликаты
				isDuplicate := false
				for _, m := range newMACs {
					if strings.EqualFold(m, mac) {
						isDuplicate = true
						break
					}
				}

				if !isDuplicate {
					// Проверка на дубликаты в существующем пуле
					for _, addr := range pool.Addresses {
						if strings.EqualFold(addr.Address, mac) {
							fmt.Printf(colorYellow+"MAC %s already exists in pool (skipped)\n"+colorReset, mac)
							isDuplicate = true
							break
						}
					}
				}

				if !isDuplicate {
					newMACs = append(newMACs, mac)
				}
			}
		}

		if scanner.Err() != nil {
			fmt.Println(colorRed+"Error scanning file:"+colorReset, scanner.Err())
		}

	default:
		fmt.Println(colorRed + "Invalid option." + colorReset)
		return errors.New("invalid option")
	}

	if len(newMACs) == 0 {
		fmt.Println(colorYellow + "No valid MAC addresses to add." + colorReset)
		return nil
	}

	// Добавление новых MAC в пул
	for _, mac := range newMACs {
		pool.Addresses = append(pool.Addresses, MACAddress{
			Address: mac,
			Used:    false,
		})
	}

	pool.LastUpdated = time.Now()

	// Обновляем HMAC подпись
	signPool(&pool, password)

	// Сохранение обновленного пула
	fmt.Printf(colorGreen+"Adding %d MAC addresses to pool.\n"+colorReset, len(newMACs))
	err = saveEncryptedPool(pool, password, poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to save pool:"+colorReset, err)
		return err
	}

	fmt.Println(colorGreen + "MAC addresses added successfully!" + colorReset)
	return nil
}

// generateMACAddresses создает MAC-адреса с указанным префиксом производителя
func generateMACAddresses(vendorPrefix string, count int, existingAddresses []MACAddress) ([]string, error) {
	// Проверка формата префикса
	if !isVendorPrefixValid(vendorPrefix) {
		return nil, errors.New("invalid vendor prefix format")
	}

	// Подготовка префикса без двоеточий для генерации
	prefix := strings.ReplaceAll(vendorPrefix, ":", "")

	// Определяем максимальное количество адресов, которые можно сгенерировать с этим префиксом
	var maxPossible uint64 = 1
	for i := 0; i < (12 - len(prefix)); i++ {
		maxPossible *= 16
	}

	if uint64(count) > maxPossible {
		return nil, fmt.Errorf("requested count exceeds maximum possible (%d) for prefix %s", maxPossible, vendorPrefix)
	}

	// Создаем карту существующих адресов для быстрой проверки дубликатов
	existingMap := make(map[string]bool)
	for _, addr := range existingAddresses {
		existingMap[strings.ToUpper(addr.Address)] = true
	}

	var generatedMACs []string
	var attempts int = 0
	maxAttempts := count * 10 // Установим максимальное количество попыток

	for len(generatedMACs) < count && attempts < maxAttempts {
		attempts++

		// Генерируем случайные байты для оставшейся части MAC-адреса
		remainingBytes := make([]byte, (12-len(prefix))/2)
		_, err := rand.Read(remainingBytes)
		if err != nil {
			return nil, fmt.Errorf("failed to generate random bytes: %v", err)
		}

		// Формируем полный MAC-адрес
		fullMAC := prefix
		for _, b := range remainingBytes {
			fullMAC += fmt.Sprintf("%02X", b)
		}

		// Преобразуем в стандартный формат с двоеточиями
		formattedMAC := formatMACWithColons(fullMAC)

		// Проверяем, что такого адреса еще нет
		if !existingMap[formattedMAC] {
			generatedMACs = append(generatedMACs, formattedMAC)
			existingMap[formattedMAC] = true
		}
	}

	if len(generatedMACs) < count {
		return generatedMACs, fmt.Errorf("could only generate %d unique addresses after %d attempts", len(generatedMACs), attempts)
	}

	return generatedMACs, nil
}

// formatMACWithColons преобразует MAC из формата без разделителей в формат с двоеточиями
func formatMACWithColons(mac string) string {
	var formatted strings.Builder
	for i := 0; i < len(mac); i += 2 {
		if i > 0 {
			formatted.WriteString(":")
		}
		formatted.WriteString(mac[i : i+2])
	}
	return formatted.String()
}

// removeMACsFromPool удаляет MAC-адреса из пула
func removeMACsFromPool(poolFile string) error {
	// Загрузка существующего пула
	pool, password, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		return err
	}

	if len(pool.Addresses) == 0 {
		fmt.Println(colorYellow + "Pool is empty, nothing to remove." + colorReset)
		return nil
	}

	// Отображение всех MAC-адресов
	fmt.Println("\nMAC addresses in pool:")
	for i, addr := range pool.Addresses {
		status := "Unused"
		if addr.Used {
			status = fmt.Sprintf("Used at %s", addr.UsedAt.Format("2006-01-02 15:04:05"))
			if addr.UsedBy != "" {
				status += fmt.Sprintf(" by %s", addr.UsedBy)
			}
		}
		if addr.Reserved {
			status += " (Reserved)"
		}

		comment := ""
		if addr.Comment != "" {
			comment = " - " + addr.Comment
		}

		fmt.Printf("%d. %s - %s%s\n", i+1, addr.Address, status, comment)
	}

	// Предложить варианты удаления
	fmt.Println("\nHow would you like to remove MAC addresses?")
	fmt.Println("1. Select by numbers")
	fmt.Println("2. Remove all unused MAC addresses")
	fmt.Println("3. Remove specific MAC address")
	fmt.Println("0. Cancel")

	var choice string
	fmt.Print("\nSelect option: ")
	fmt.Scanln(&choice)

	var indicesToRemove []int

	switch choice {
	case "0":
		fmt.Println("Operation cancelled.")
		return nil
	case "1":
		// Выбор по номерам
		fmt.Println("Enter numbers of MAC addresses to remove (comma separated, e.g. 1,3,5):")
		scanner := bufio.NewScanner(os.Stdin)
		scanner.Scan()
		input := strings.TrimSpace(scanner.Text())

		for _, numStr := range strings.Split(input, ",") {
			var idx int
			_, err := fmt.Sscanf(numStr, "%d", &idx)
			if err != nil || idx < 1 || idx > len(pool.Addresses) {
				fmt.Printf(colorYellow+"Invalid index: %s (skipped)\n"+colorReset, numStr)
				continue
			}
			indicesToRemove = append(indicesToRemove, idx-1) // -1 для индекса массива
		}

	case "2":
		// Удаление всех неиспользуемых
		fmt.Print("Are you sure you want to remove ALL unused MAC addresses? (yes/no): ")
		var confirm string
		fmt.Scanln(&confirm)
		if strings.ToLower(confirm) != "yes" {
			fmt.Println("Operation cancelled.")
			return nil
		}

		for i, addr := range pool.Addresses {
			if !addr.Used && !addr.Reserved {
				indicesToRemove = append(indicesToRemove, i)
			}
		}

	case "3":
		// Удаление конкретного MAC
		fmt.Print("Enter MAC address to remove: ")
		scanner := bufio.NewScanner(os.Stdin)
		scanner.Scan()
		targetMAC := strings.TrimSpace(scanner.Text())

		if !isMACValid(targetMAC) {
			fmt.Println(colorRed + "Invalid MAC address format." + colorReset)
			return errors.New("invalid MAC format")
		}

		// Стандартизация формата для сравнения
		targetMAC = standardizeMACFormat(targetMAC)

		found := false
		for i, addr := range pool.Addresses {
			if strings.EqualFold(addr.Address, targetMAC) {
				indicesToRemove = append(indicesToRemove, i)
				found = true
				break
			}
		}

		if !found {
			fmt.Println(colorRed + "MAC address not found in pool." + colorReset)
			return errors.New("MAC not found")
		}

	default:
		fmt.Println(colorRed + "Invalid option." + colorReset)
		return errors.New("invalid option")
	}

	if len(indicesToRemove) == 0 {
		fmt.Println(colorYellow + "No MAC addresses selected for removal." + colorReset)
		return nil
	}

	// Подтверждение для использованных адресов
	var usedCount int
	for _, idx := range indicesToRemove {
		if pool.Addresses[idx].Used {
			usedCount++
		}
	}

	if usedCount > 0 {
		fmt.Printf(colorYellow+"Warning: %d of the selected MAC addresses are marked as used.\n"+colorReset, usedCount)
		fmt.Print("Are you sure you want to remove them? (yes/no): ")
		var confirm string
		fmt.Scanln(&confirm)
		if strings.ToLower(confirm) != "yes" {
			fmt.Println("Removing only unused MAC addresses.")
			// Фильтруем для удаления только неиспользуемых
			var filteredIndices []int
			for _, idx := range indicesToRemove {
				if !pool.Addresses[idx].Used {
					filteredIndices = append(filteredIndices, idx)
				}
			}
			indicesToRemove = filteredIndices
		}
	}

	// Удаление MAC-адресов (в обратном порядке, чтобы не нарушить индексацию)
	sort.Ints(indicesToRemove)
	for i := len(indicesToRemove) - 1; i >= 0; i-- {
		idx := indicesToRemove[i]
		if idx >= 0 && idx < len(pool.Addresses) {
			// Удаляем элемент
			pool.Addresses = append(pool.Addresses[:idx], pool.Addresses[idx+1:]...)
		}
	}

	pool.LastUpdated = time.Now()

	// Обновляем HMAC подпись
	signPool(&pool, password)

	// Сохранение обновленного пула
	fmt.Printf(colorGreen+"Removing %d MAC addresses from pool.\n"+colorReset, len(indicesToRemove))
	err = saveEncryptedPool(pool, password, poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to save pool:"+colorReset, err)
		return err
	}

	fmt.Println(colorGreen + "MAC addresses removed successfully!" + colorReset)
	return nil
}

// listMACsInPool выводит список MAC-адресов в пуле
func listMACsInPool(poolFile string) error {
	// Загрузка существующего пула
	pool, _, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		return err
	}

	if len(pool.Addresses) == 0 {
		fmt.Println(colorYellow + "Pool is empty." + colorReset)
		return nil
	}

	// Предложить варианты отображения
	fmt.Println("\nHow would you like to view MAC addresses?")
	fmt.Println("1. View all MAC addresses")
	fmt.Println("2. View only unused MAC addresses")
	fmt.Println("3. View only used MAC addresses")
	fmt.Println("0. Cancel")

	var choice string
	fmt.Print("\nSelect option: ")
	fmt.Scanln(&choice)

	var filteredAddresses []MACAddress

	switch choice {
	case "0":
		return nil
	case "1":
		filteredAddresses = pool.Addresses
	case "2":
		for _, addr := range pool.Addresses {
			if !addr.Used {
				filteredAddresses = append(filteredAddresses, addr)
			}
		}
	case "3":
		for _, addr := range pool.Addresses {
			if addr.Used {
				filteredAddresses = append(filteredAddresses, addr)
			}
		}
	default:
		fmt.Println(colorRed + "Invalid option." + colorReset)
		return errors.New("invalid option")
	}

	// Отображение MAC-адресов
	fmt.Println("\nMAC addresses in pool:")
	if len(filteredAddresses) == 0 {
		fmt.Println(colorYellow + "No MAC addresses matching the selected filter." + colorReset)
		return nil
	}

	for i, addr := range filteredAddresses {
		status := "Unused"
		if addr.Used {
			status = fmt.Sprintf("Used at %s", addr.UsedAt.Format("2006-01-02 15:04:05"))
			if addr.UsedBy != "" {
				status += fmt.Sprintf(" by %s", addr.UsedBy)
			}
		}
		if addr.Reserved {
			status += " (Reserved)"
		}

		comment := ""
		if addr.Comment != "" {
			comment = " - " + addr.Comment
		}

		fmt.Printf("%d. %s - %s%s\n", i+1, addr.Address, status, comment)
	}

	// Статистика
	unusedCount := 0
	usedCount := 0
	reservedCount := 0

	for _, addr := range pool.Addresses {
		if addr.Used {
			usedCount++
		} else if addr.Reserved {
			reservedCount++
		} else {
			unusedCount++
		}
	}

	fmt.Printf("\nSummary: %d total MAC addresses, %d used, %d unused, %d reserved\n",
		len(pool.Addresses), usedCount, unusedCount, reservedCount)
	fmt.Printf("Last updated: %s\n", pool.LastUpdated.Format("2006-01-02 15:04:05"))
	fmt.Printf("Created by: %s\n", pool.CreatedBy)

	if pool.MACVendorPrefix != "" {
		fmt.Printf("Vendor prefix: %s\n", pool.MACVendorPrefix)
	}

	return nil
}

// resetMACStatus сбрасывает статус MAC-адреса (помечает как неиспользуемый)
func resetMACStatus(poolFile string) error {
	// Загрузка существующего пула
	pool, password, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		return err
	}

	// Проверка наличия использованных MAC-адресов
	var usedAddresses []int
	for i, addr := range pool.Addresses {
		if addr.Used {
			usedAddresses = append(usedAddresses, i)
		}
	}

	if len(usedAddresses) == 0 {
		fmt.Println(colorYellow + "No used MAC addresses in pool." + colorReset)
		return nil
	}

	// Отображение всех использованных MAC-адресов
	fmt.Println("\nUsed MAC addresses in pool:")
	for i, idx := range usedAddresses {
		addr := pool.Addresses[idx]
		fmt.Printf("%d. %s - Used at %s", i+1, addr.Address, addr.UsedAt.Format("2006-01-02 15:04:05"))
		if addr.UsedBy != "" {
			fmt.Printf(" by %s", addr.UsedBy)
		}
		fmt.Println()
	}

	// Предложить варианты сброса
	fmt.Println("\nHow would you like to reset MAC addresses?")
	fmt.Println("1. Select by numbers")
	fmt.Println("2. Reset all used MAC addresses")
	fmt.Println("0. Cancel")

	var choice string
	fmt.Print("\nSelect option: ")
	fmt.Scanln(&choice)

	var indicesToReset []int

	switch choice {
	case "0":
		fmt.Println("Operation cancelled.")
		return nil
	case "1":
		// Выбор по номерам
		fmt.Println("Enter numbers of MAC addresses to reset (comma separated, e.g. 1,3,5):")
		scanner := bufio.NewScanner(os.Stdin)
		scanner.Scan()
		input := strings.TrimSpace(scanner.Text())

		for _, numStr := range strings.Split(input, ",") {
			var idx int
			_, err := fmt.Sscanf(numStr, "%d", &idx)
			if err != nil || idx < 1 || idx > len(usedAddresses) {
				fmt.Printf(colorYellow+"Invalid index: %s (skipped)\n"+colorReset, numStr)
				continue
			}
			indicesToReset = append(indicesToReset, usedAddresses[idx-1]) // Получаем реальный индекс из списка использованных
		}

	case "2":
		// Сброс всех
		fmt.Print("Are you sure you want to reset ALL used MAC addresses? (yes/no): ")
		var confirm string
		fmt.Scanln(&confirm)
		if strings.ToLower(confirm) != "yes" {
			fmt.Println("Operation cancelled.")
			return nil
		}

		indicesToReset = usedAddresses

	default:
		fmt.Println(colorRed + "Invalid option." + colorReset)
		return errors.New("invalid option")
	}

	if len(indicesToReset) == 0 {
		fmt.Println(colorYellow + "No MAC addresses selected for reset." + colorReset)
		return nil
	}

	// Сброс статуса MAC-адресов
	resetCount := 0
	for _, idx := range indicesToReset {
		if idx >= 0 && idx < len(pool.Addresses) {
			if pool.Addresses[idx].Used {
				pool.Addresses[idx].Used = false
				pool.Addresses[idx].UsedAt = time.Time{}
				pool.Addresses[idx].UsedBy = ""
				resetCount++
			}
		}
	}

	pool.LastUpdated = time.Now()

	// Обновляем HMAC подпись
	signPool(&pool, password)

	// Сохранение обновленного пула
	fmt.Printf(colorGreen+"Resetting %d MAC addresses status.\n"+colorReset, resetCount)
	err = saveEncryptedPool(pool, password, poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to save pool:"+colorReset, err)
		return err
	}

	fmt.Println(colorGreen + "MAC addresses reset successfully!" + colorReset)
	return nil
}

// changePassword изменяет пароль шифрования для пула
func changePassword(poolFile string) error {
	// Загрузка существующего пула
	pool, oldPassword, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		return err
	}

	// Запрос нового пароля
	fmt.Print("Enter new password: ")
	newPassword, err := term.ReadPassword(int(syscall.Stdin))
	fmt.Println()
	if err != nil {
		fmt.Println(colorRed+"Failed to read password:"+colorReset, err)
		return err
	}

	// Подтверждение нового пароля
	fmt.Print("Confirm new password: ")
	confirmPassword, err := term.ReadPassword(int(syscall.Stdin))
	fmt.Println()
	if err != nil {
		fmt.Println(colorRed+"Failed to read password:"+colorReset, err)
		return err
	}

	if string(newPassword) != string(confirmPassword) {
		fmt.Println(colorRed + "Passwords do not match!" + colorReset)
		return errors.New("passwords do not match")
	}

	if len(newPassword) < 8 {
		fmt.Println(colorRed + "Password must be at least 8 characters long!" + colorReset)
		return errors.New("password too short")
	}

	// Обновляем HMAC подпись с новым паролем
	signPool(&pool, string(newPassword))

	// Сохранение с новым паролем
	err = saveEncryptedPool(pool, string(newPassword), poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to save pool with new password:"+colorReset, err)
		// Пытаемся восстановить предыдущее состояние
		signPool(&pool, oldPassword)
		_ = saveEncryptedPool(pool, oldPassword, poolFile)
		return err
	}

	fmt.Println(colorGreen + "Password changed successfully!" + colorReset)
	return nil
}

// exportPoolStats экспортирует статистику пула MAC-адресов
func exportPoolStats(poolFile string) error {
	// Загрузка существующего пула
	pool, _, err := loadAndDecryptPool(poolFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to load MAC pool:"+colorReset, err)
		return err
	}

	// Сбор статистики
	unusedCount := 0
	usedCount := 0
	reservedCount := 0

	for _, addr := range pool.Addresses {
		if addr.Used {
			usedCount++
		} else if addr.Reserved {
			reservedCount++
		} else {
			unusedCount++
		}
	}

	// Создание файла отчета
	timeStr := time.Now().Format("20060102_150405")
	statsFile := filepath.Join(filepath.Dir(poolFile), fmt.Sprintf("mac_pool_stats_%s.txt", timeStr))

	f, err := os.Create(statsFile)
	if err != nil {
		fmt.Println(colorRed+"Failed to create stats file:"+colorReset, err)
		return err
	}
	defer f.Close()

	// Запись статистики
	f.WriteString("MAC Address Pool Statistics\n")
	f.WriteString("==========================\n\n")
	f.WriteString(fmt.Sprintf("Export date: %s\n", time.Now().Format("2006-01-02 15:04:05")))
	f.WriteString(fmt.Sprintf("Pool file: %s\n", poolFile))
	f.WriteString(fmt.Sprintf("Created by: %s\n", pool.CreatedBy))
	f.WriteString(fmt.Sprintf("Last updated: %s\n\n", pool.LastUpdated.Format("2006-01-02 15:04:05")))

	f.WriteString("Summary:\n")
	f.WriteString(fmt.Sprintf("Total MAC addresses: %d\n", len(pool.Addresses)))
	f.WriteString(fmt.Sprintf("Used: %d (%.1f%%)\n", usedCount, float64(usedCount)/float64(len(pool.Addresses))*100))
	f.WriteString(fmt.Sprintf("Unused: %d (%.1f%%)\n", unusedCount, float64(unusedCount)/float64(len(pool.Addresses))*100))
	f.WriteString(fmt.Sprintf("Reserved: %d (%.1f%%)\n\n", reservedCount, float64(reservedCount)/float64(len(pool.Addresses))*100))

	if pool.MACVendorPrefix != "" {
		f.WriteString(fmt.Sprintf("Vendor prefix: %s\n\n", pool.MACVendorPrefix))
	}

	// Запрос опция для детального экспорта
	fmt.Println("\nWould you like to include the full list of MAC addresses in the export?")
	fmt.Println("1. No, just summary statistics")
	fmt.Println("2. Yes, include all MAC addresses")
	fmt.Println("3. Yes, but only used MAC addresses")
	fmt.Println("4. Yes, but only unused MAC addresses")

	var choice string
	fmt.Print("\nSelect option: ")
	fmt.Scanln(&choice)

	switch choice {
	case "2", "3", "4":
		f.WriteString("MAC Address List:\n")
		f.WriteString("----------------\n\n")

		for i, addr := range pool.Addresses {
			include := false

			switch choice {
			case "2": // Все
				include = true
			case "3": // Только использованные
				include = addr.Used
			case "4": // Только неиспользованные
				include = !addr.Used && !addr.Reserved
			}

			if include {
				status := "Unused"
				if addr.Used {
					status = fmt.Sprintf("Used at %s", addr.UsedAt.Format("2006-01-02 15:04:05"))
					if addr.UsedBy != "" {
						status += fmt.Sprintf(" by %s", addr.UsedBy)
					}
				}
				if addr.Reserved {
					status += " (Reserved)"
				}

				comment := ""
				if addr.Comment != "" {
					comment = " - " + addr.Comment
				}

				f.WriteString(fmt.Sprintf("%d. %s - %s%s\n", i+1, addr.Address, status, comment))
			}
		}
	}

	fmt.Printf(colorGreen+"Statistics exported to: %s\n"+colorReset, statsFile)
	return nil
}

// loadAndDecryptPool загружает и дешифрует пул MAC-адресов
func loadAndDecryptPool(poolFile string) (MACPool, string, error) {
	var pool MACPool

	// Проверка существования файла
	if _, err := os.Stat(poolFile); os.IsNotExist(err) {
		return pool, "", errors.New("MAC address pool file does not exist")
	}

	// Чтение зашифрованных данных
	encryptedData, err := os.ReadFile(poolFile)
	if err != nil {
		return pool, "", fmt.Errorf("failed to read MAC pool file: %v", err)
	}

	// Запрос пароля для дешифрования
	fmt.Print("Enter password: ")
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
func saveEncryptedPool(pool MACPool, password, poolFile string) error {
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

	// Создание директории, если она не существует
	dir := filepath.Dir(poolFile)
	if _, err := os.Stat(dir); os.IsNotExist(err) {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return fmt.Errorf("failed to create directory: %v", err)
		}
	}

	// Сохранение в файл
	if err := os.WriteFile(poolFile, encryptedData, 0600); err != nil {
		return fmt.Errorf("failed to write MAC pool file: %v", err)
	}

	fmt.Printf(colorGreen+"[INFO] MAC address pool saved to %s\n"+colorReset, poolFile)
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

// isMACValid проверяет, соответствует ли строка формату MAC-адреса
func isMACValid(mac string) bool {
	re := regexp.MustCompile(`^([0-9A-Fa-f]{2}[:-]){5}[0-9A-Fa-f]{2}$`)
	return re.MatchString(mac)
}

// isVendorPrefixValid проверяет, соответствует ли строка формату префикса производителя
func isVendorPrefixValid(prefix string) bool {
	re := regexp.MustCompile(`^([0-9A-Fa-f]{2}[:-]){2}[0-9A-Fa-f]{2}$`)
	return re.MatchString(prefix)
}

// standardizeMACFormat стандартизирует формат MAC-адреса (переводит в верхний регистр и использует : как разделитель)
func standardizeMACFormat(mac string) string {
	// Преобразуем в верхний регистр
	mac = strings.ToUpper(mac)

	// Заменяем - на : если нужно
	if strings.Contains(mac, "-") {
		mac = strings.ReplaceAll(mac, "-", ":")
	}

	return mac
}

// waitForEnter ожидает нажатия клавиши Enter
func waitForEnter(message string) {
	if message == "" {
		message = "Press ENTER to continue..."
	}
	fmt.Println(message)
	bufio.NewReader(os.Stdin).ReadString('\n')
}

// showErrorAndWait показывает сообщение об ошибке и ждет нажатия Enter
func showErrorAndWait(err error) {
	fmt.Println(colorRed + "Error: " + err.Error() + colorReset)
	waitForEnter("")
}

// readUserInput читает ввод пользователя с приглашением
func readUserInput(prompt string) (string, error) {
	fmt.Print(prompt)
	reader := bufio.NewReader(os.Stdin)
	input, err := reader.ReadString('\n')
	if err != nil {
		return "", err
	}
	return strings.TrimSpace(input), nil
}

// getYesNoConfirmation запрашивает подтверждение да/нет у пользователя
func getYesNoConfirmation(prompt string) bool {
	for {
		input, err := readUserInput(prompt + " (yes/no): ")
		if err != nil {
			fmt.Println(colorYellow + "Error reading input. Please try again." + colorReset)
			continue
		}

		input = strings.ToLower(input)
		if input == "yes" || input == "y" {
			return true
		} else if input == "no" || input == "n" {
			return false
		}

		fmt.Println(colorYellow + "Please answer 'yes' or 'no'." + colorReset)
	}
}
