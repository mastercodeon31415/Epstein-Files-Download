# Epstein Files Download / DOJ Archive Scraper

![License](https://img.shields.io/badge/license-MIT-blue.svg) ![Platform](https://img.shields.io/badge/platform-.NET-purple.svg) ![Status](https://img.shields.io/badge/status-active-success.svg)

## 📁 The Ultimate Epstein & Maxwell Archive Downloader

**Epstein Files Download** is a specialized, high-performance C# console application designed to scrape, organize, and download the complete collection of declassified documents regarding Jeffrey Epstein and Ghislaine Maxwell hosted on the United States Department of Justice (DOJ) website.

This tool automates the retrieval of thousands of pages of court records, flight logs, FOIA releases, and multimedia evidence (videos/audio), ensuring a complete local backup of this historical data.

### 🚀 Key Features

*   **🛡️ Security Bypass (User-Agent Spoofing):**
    *   The DOJ web servers are configured to block standard programmatic requests (returning HTTP 404/403 errors to standard .NET/Python web clients).
    *   This tool bypasses these restrictions by strictly masquerading as `curl/7.68.0` in the HTTP headers, allowing uninhibited access to the files.
*   **⚡ Adaptive "Smart" Threading Engine:**
    *   **Large Files (>50MB):** Automatically detects large files (like the BOP video footage or massive PDFs) and utilizes **8 dedicated threads** to download the file in chunks simultaneously (Range Processing).
    *   **Small Files:** Switches strategy to download multiple small files in parallel (1 thread per file), maximizing bandwidth without overloading the host.
*   **📂 Intelligent Organization:**
    *   Parses the DOJ's complex "Accordion" HTML structure to correctly categorize files.
    *   Automatically sorts downloads into clean directories (e.g., `Epstein Files Transparency Act`, `Maxwell Proffer`, `Flight Logs`, `Court Records`).
*   **🔄 Resilience:**
    *   Built-in retry logic (3 attempts) for failed connections.
    *   Detailed logging of any skipped or failed files.

---

## 🛠️ Technical Deep Dive

### WAF / Security Evasion
Many government servers employ basic filtering to prevent bot scraping. If you attempt to access these PDF links using a standard `HttpClient` in C#, the server often returns a **404 Not Found** (false negative).

This tool solves this by modifying the request headers for every single interaction:

```csharp
_httpClient.DefaultRequestHeaders.TryAddWithoutValidation("User-Agent", "curl/7.68.0");
_httpClient.DefaultRequestHeaders.TryAddWithoutValidation("Accept", "*/*");
```

By emulating the footprint of the `curl` command-line utility, the scraper is granted access to files that are otherwise "hidden" from automated tools.

### Adaptive Downloader Logic
The program analyzes the `Content-Length` header via a `HEAD` request before downloading:

| File Size | Strategy | Description |
| :--- | :--- | :--- |
| **< 50 MB** | `Standard` | Uses 1 thread per file. Multiple files are downloaded concurrently to fill the UI slots. |
| **> 50 MB** | `Accelerated` | The file is split into 8 byte-ranges. 8 threads download these chunks simultaneously and merge them on disk. |

---

## 📥 Installation & Usage

### Prerequisites
*   Windows OS (Preferred) or Linux/Mac with .NET Core installed.
*   .NET SDK (6.0, 7.0, or 8.0).

### Build from Source
1.  Clone this repository:
    ```bash
    git clone https://github.com/YourUsername/Epstein-Files-Download.git
    ```
2.  Navigate to the directory:
    ```bash
    cd Epstein-Files-Download
    ```
3.  Build and Run:
    ```bash
    dotnet run
    ```

### Output
The tool will create a `Epstein Files` folder in the execution directory. Inside, you will find the organized archive:

```text
Epstein Files/
├── Court Records/
│   ├── unsealed_doc_1.pdf
│   └── ...
├── DOJ Disclosures/
│   ├── Epstein Files Transparency Act (H.R.4405)/
│   │   ├── DataSet 1.zip
│   │   └── ...
│   ├── Maxwell Proffer/
│   │   ├── Interview Transcript.pdf
│   │   └── Audio_Evidence.wav
│   └── BOP Video Footage/
│       └── cell_video_enhanced.mp4
└── FOIA/
    └── ...
```

---

## ⚠️ Disclaimer

This tool is provided for **educational and archival purposes only**. The data downloaded consists of public records released by the United States Department of Justice. The author of this tool is not affiliated with the DOJ. Please respect server load by not running multiple instances of this tool simultaneously.

---

## 🤝 Contributing

Pull requests are welcome. For major changes, please open an issue first to discuss what you would like to change.
```

---