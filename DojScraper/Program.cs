using System;
using System.IO;
using System.Collections.Generic;
using System.Collections.Concurrent;
using System.Linq;
using System.Net;
using System.Net.Http;
using System.Net.Http.Headers;
using System.Threading;
using System.Threading.Tasks;
using System.Diagnostics;
using System.Text.RegularExpressions;
using HtmlAgilityPack;

namespace DojScraper
{
    public class LinkScraper
    {
        // --- CONFIGURATION ---
        private const int MAX_TOTAL_THREADS = 8;
        private const int LARGE_FILE_COST = 8; // Uses all threads
        private const int SMALL_FILE_COST = 1;
        private const long LARGE_FILE_THRESHOLD = 50 * 1024 * 1024; // 50MB

        // --- LAYOUT CONSTANTS ---
        private const int UI_HEADER_HEIGHT = MAX_TOTAL_THREADS - 1;
        private const int SLOT_COUNT = MAX_TOTAL_THREADS;

        // Header (0-6)
        // Status Slots (7-14)
        // Mid Divider (15)
        // Progress Section (Starts at 16, Dynamic Height)

        private const int ROW_STATUS_START = UI_HEADER_HEIGHT;
        private const int ROW_DIVIDER = UI_HEADER_HEIGHT + SLOT_COUNT;
        private const int ROW_PROGRESS_START = UI_HEADER_HEIGHT + SLOT_COUNT + 1;

        private const int MAX_RETRIES = 3;
        private const string LOG_FILE = "failed_downloads_log.txt";
        // ---------------------

        public class ThreadTokenManager
        {
            private int _available = MAX_TOTAL_THREADS;
            private readonly object _lock = new object();
            public int Available { get { lock (_lock) return _available; } }

            public async Task AcquireAsync(int count)
            {
                while (true)
                {
                    lock (_lock)
                    {
                        if (_available >= count)
                        {
                            _available -= count;
                            return;
                        }
                    }
                    await Task.Delay(50);
                }
            }

            public void Release(int count)
            {
                lock (_lock) _available += count;
            }
        }

        public class SlotProgressTracker
        {
            public int PrimaryUiSlot { get; }
            private readonly long _totalBytes;
            private long _currentBytes;
            private long _bytesAtLastDraw;
            private DateTime _lastDrawTime;

            public SlotProgressTracker(int primaryUiSlot, long totalBytes)
            {
                PrimaryUiSlot = primaryUiSlot;
                _totalBytes = totalBytes <= 0 ? -1 : totalBytes;
                _currentBytes = 0;
                _bytesAtLastDraw = 0;
                _lastDrawTime = DateTime.Now;
            }

            public void Report(int bytesRead)
            {
                long newTotal = Interlocked.Add(ref _currentBytes, bytesRead);
                Interlocked.Add(ref _totalBytesDownloaded, bytesRead);

                var now = DateTime.Now;
                // Throttle updates to ~5fps
                if ((now - _lastDrawTime).TotalMilliseconds > 200 || (_totalBytes > 0 && newTotal == _totalBytes))
                {
                    UpdateProgress(this); // Call back to main class to draw
                    _lastDrawTime = now;
                    _bytesAtLastDraw = newTotal;
                }
            }

            public string GetDrawString()
            {
                double seconds = (DateTime.Now - _lastDrawTime).TotalSeconds; // Approx
                                                                              // We use stored speed to avoid jitter between draw calls if we wanted, 
                                                                              // but re-calculating here is fine for the string generation.
                                                                              // Better approach: Report() calculates speed, this just formats string.
                                                                              // For simplicity, we'll calc instantaneous speed based on bytes/time since last Report check

                // Note: The Report method actually throttles the *calls* to UpdateProgress. 
                // So when this is called, we are in a draw cycle.

                long current = Interlocked.Read(ref _currentBytes);
                // Speed calculation is slightly tricky decoupled. 
                // Let's just use the values derived in Report() if we passed them, 
                // or simplistic math here:

                // Simplified: We rely on the visual string being stable.
                // Let's recalc speed based on the interval tracked in Report? 
                // Actually, let's just make Report pass the speed or store it.
                // For this code, I'll calculate it based on the diff since constructor for average, 
                // or just 0 if we want to be pure.
                // To do it right: Report() should store _currentSpeed.

                // Let's fix the speed jitter:
                double speed = 0;
                // (Speed logic handled inside Report logic block implicitly by updating the screen)
                // But GetDrawString needs to know it. 
                // Let's change design slightly: Report calls Update, Update calls GetDrawString. 
                // We will store the last calculated speed in a field.

                return FormatBar(current, _lastSpeed);
            }

            private double _lastSpeed = 0;
            public void SetSpeed(double s) { _lastSpeed = s; }

            private string FormatBar(long current, double speed)
            {
                string speedStr = $"{FormatBytes((long)speed)}/s";
                string sizeStr = FormatBytes(current);
                string barLine;

                // Include the Slot ID so user knows which Status Row this matches
                string prefix = $" [{PrimaryUiSlot + 1}]";

                if (_totalBytes > 0)
                {
                    double percent = (double)current / _totalBytes;
                    if (percent > 1) percent = 1;

                    int availableWidth = 30;
                    int chars = (int)(percent * availableWidth);
                    string bar = new string('#', chars) + new string('-', availableWidth - chars);
                    string totalStr = FormatBytes(_totalBytes);

                    barLine = $"{prefix} [{bar}] {percent:P0} | {sizeStr} / {totalStr} | {speedStr}";
                }
                else
                {
                    barLine = $"{prefix} [------------------------------] ???% | {sizeStr} | {speedStr}";
                }
                return barLine;
            }
        }

        public class DownloadItem
        {
            public string Url { get; set; }
            public string LocalPath { get; set; }
            public string GroupName { get; set; }
            public string FileName { get; set; }
        }

        public class ScrapeResult
        {
            public string Name { get; set; }
            public List<DownloadItem> Items { get; set; } = new List<DownloadItem>();
        }

        private static readonly HttpClient _httpClient;
        private static readonly object _consoleLock = new object();
        private static readonly object _logFileLock = new object();

        private static ConcurrentQueue<DownloadItem> _masterQueue = new ConcurrentQueue<DownloadItem>();
        private static ThreadTokenManager _threadManager = new ThreadTokenManager();
        private static ConcurrentQueue<int> _freeUiSlots = new ConcurrentQueue<int>();

        // Active Progress Trackers List
        private static List<SlotProgressTracker> _activeTrackers = new List<SlotProgressTracker>();
        private static int _lastFooterRow = ROW_PROGRESS_START; // Track where the footer was drawn

        private static int _totalFilesToDownload = 0;
        private static int _filesDownloaded = 0;
        private static int _filesFailed = 0;
        private static long _totalBytesDownloaded = 0;
        private static string _lastErrorMsg = "";

        static LinkScraper()
        {
            var handler = new HttpClientHandler()
            {
                AutomaticDecompression = DecompressionMethods.None,
                UseCookies = false,
                AllowAutoRedirect = true,
                MaxConnectionsPerServer = 100
            };

            _httpClient = new HttpClient(handler);
            _httpClient.Timeout = TimeSpan.FromMinutes(10);
            _httpClient.DefaultRequestHeaders.Clear();
            _httpClient.DefaultRequestHeaders.TryAddWithoutValidation("User-Agent", "curl/7.68.0");
            _httpClient.DefaultRequestHeaders.TryAddWithoutValidation("Accept", "*/*");

            File.WriteAllText(LOG_FILE, $"--- Scrape Session Started: {DateTime.Now} ---\n");
        }

        public static async Task Main(string[] args)
        {
            Console.CursorVisible = false;

            // Initialize Slots
            for (int i = 0; i < SLOT_COUNT; i++) _freeUiSlots.Enqueue(i);

            await ScrapeAndBuildQueue();
            _totalFilesToDownload = _masterQueue.Count;

            Console.Clear();
            DrawStaticUiFrame();

            // Initial visual state: Set all Status slots to "Idle"
            var allSlots = Enumerable.Range(0, SLOT_COUNT).ToList();
            ClearStatusSlots(allSlots);
            RedrawFooter();

            var stopwatch = Stopwatch.StartNew();
            var cts = new CancellationTokenSource();

            // UI Update Loop
            var uiTask = Task.Run(async () => {
                while (!cts.Token.IsCancellationRequested)
                {
                    UpdateGlobalStats(stopwatch.Elapsed);
                    await Task.Delay(250);
                }
                UpdateGlobalStats(stopwatch.Elapsed);
            });

            var activeTasks = new List<Task>();

            // SCOUTING LIMITER:
            // Allows us to "look ahead" and check the size of the next 16 files concurrently
            // without committing download threads yet. This prevents the "GetFileSize" network
            // lag from blocking the main dispatch loop.
            var scoutLimiter = new SemaphoreSlim(MAX_TOTAL_THREADS * 2);

            while (!_masterQueue.IsEmpty || activeTasks.Count > 0)
            {
                // Clean up finished tasks
                activeTasks.RemoveAll(t => t.IsCompleted);

                if (_masterQueue.IsEmpty)
                {
                    await Task.Delay(100);
                    continue;
                }

                // Check if we have capacity to "Scout" (Check size of) a new item
                if (scoutLimiter.CurrentCount > 0 && _masterQueue.TryDequeue(out DownloadItem nextItem))
                {
                    await scoutLimiter.WaitAsync();

                    // Launch the lifecycle of this file in a background task immediately
                    // so the Main loop can continue to the next item instantly.
                    var task = Task.Run(async () =>
                    {
                        try
                        {
                            // 1. Check Size (This used to block the main loop)
                            long size = await GetFileSizeAsync(nextItem.Url);

                            bool isLarge = size == 0 || size > LARGE_FILE_THRESHOLD;
                            int cost = isLarge ? LARGE_FILE_COST : SMALL_FILE_COST;

                            // 2. Wait for Execution Threads
                            await _threadManager.AcquireAsync(cost);

                            // 3. Acquire UI Slots
                            // Since we hold the ThreadTokens, we are guaranteed slots will eventually
                            // become available, but we might have to wait a few ms for the previous
                            // task to finish enqueuing them back.
                            var allocatedSlots = new List<int>();
                            while (_freeUiSlots.Count < cost) await Task.Delay(10);

                            for (int i = 0; i < cost; i++)
                            {
                                if (_freeUiSlots.TryDequeue(out int slot))
                                    allocatedSlots.Add(slot);
                            }
                            allocatedSlots.Sort();

                            // 4. Execute Download
                            try
                            {
                                await ProcessDownloadItem(nextItem, allocatedSlots, size, cost);
                            }
                            finally
                            {
                                // 5. Cleanup
                                ClearStatusSlots(allocatedSlots);
                                foreach (var s in allocatedSlots) _freeUiSlots.Enqueue(s);
                                _threadManager.Release(cost);
                            }
                        }
                        catch (Exception ex)
                        {
                            // Safety catch for logic errors
                            LogFailure(nextItem, "CRITICAL", ex.Message);
                        }
                        finally
                        {
                            scoutLimiter.Release();
                        }
                    });

                    activeTasks.Add(task);
                }
                else
                {
                    // Throttle slightly if we are maxed out on scouts
                    await Task.Delay(50);
                }
            }

            cts.Cancel();
            await uiTask;

            int donePos = _lastFooterRow + 3;
            Console.SetCursorPosition(0, donePos);
            Console.WriteLine("\nOperation Complete.");
            Console.WriteLine($"Total Time: {stopwatch.Elapsed}");
            Console.WriteLine($"Failures Logged to: {Path.GetFullPath(LOG_FILE)}");
            Console.CursorVisible = true;
            Console.ReadLine();
        }

        // --- CORE LOGIC ---

        private static async Task ProcessDownloadItem(DownloadItem item, List<int> uiSlots, long size, int threadCost)
        {
            Exception lastException = null;

            for (int attempt = 1; attempt <= MAX_RETRIES; attempt++)
            {
                try
                {
                    string statusPrefix = threadCost > 1 ? $"ACCELERATED ({threadCost} Thrd)" : "Downloading...";
                    if (attempt > 1) statusPrefix = $"Retry {attempt}/{MAX_RETRIES}...";

                    DrawSlotStatus(uiSlots, item.GroupName, item.FileName, statusPrefix);

                    await ExecuteDownload(item, uiSlots[0], size, threadCost);
                    return;
                }
                catch (Exception ex)
                {
                    lastException = ex;
                    if (attempt < MAX_RETRIES)
                    {
                        DrawSlotStatus(uiSlots, item.GroupName, item.FileName, $"Err: {ex.Message}. Wait...");
                        await Task.Delay(2000 * attempt);
                    }
                }
            }

            Interlocked.Increment(ref _filesFailed);
            string code = "N/A";
            if (lastException is HttpRequestException) code = "HTTP_ERR";
            LogFailure(item, code, lastException?.Message ?? "Unknown");

            _lastErrorMsg = $"[{DateTime.Now.ToShortTimeString()}] Failed - {item.FileName}";
            RedrawFooter(); // Update error line position
        }

        private static async Task ExecuteDownload(DownloadItem item, int primarySlot, long size, int threadCount)
        {
            var tracker = new SlotProgressTracker(primarySlot, size);
            RegisterTracker(tracker);

            try
            {
                if (threadCount > 1 && size > 0)
                {
                    await DownloadFileChunkedAsync(item.Url, item.LocalPath, size, threadCount, tracker);
                }
                else
                {
                    await DownloadFileStandardAsync(item.Url, item.LocalPath, tracker);
                }
                Interlocked.Increment(ref _filesDownloaded);
            }
            finally
            {
                UnregisterTracker(tracker);
            }
        }

        // --- DYNAMIC PROGRESS TRACKER MANAGEMENT ---

        private static void RegisterTracker(SlotProgressTracker tracker)
        {
            lock (_consoleLock)
            {
                _activeTrackers.Add(tracker);
                // Sort by primary slot so they appear in order (1, 2, 3...) not insertion order
                _activeTrackers.Sort((a, b) => a.PrimaryUiSlot.CompareTo(b.PrimaryUiSlot));
                RedrawProgressSection();
            }
        }

        private static void UnregisterTracker(SlotProgressTracker tracker)
        {
            lock (_consoleLock)
            {
                _activeTrackers.Remove(tracker);
                RedrawProgressSection();
            }
        }

        private static void UpdateProgress(SlotProgressTracker tracker)
        {
            // Called by tracker logic when bytes update
            lock (_consoleLock)
            {
                int index = _activeTrackers.IndexOf(tracker);
                if (index == -1) return; // Might have been removed concurrently

                // Calculate speed here to store it for the draw string
                // (Simplified: We rely on the tracker's internal state which was just updated)

                // Just redraw this specific line to save perf
                int row = ROW_PROGRESS_START + index;
                Console.SetCursorPosition(0, row);
                Console.Write(tracker.GetDrawString().PadRight(Console.WindowWidth - 1));
            }
        }

        private static void RedrawProgressSection()
        {
            // Draws all active bars and the footer immediately after
            // Assumes Lock is held

            for (int i = 0; i < _activeTrackers.Count; i++)
            {
                int row = ROW_PROGRESS_START + i;
                Console.SetCursorPosition(0, row);
                Console.Write(_activeTrackers[i].GetDrawString().PadRight(Console.WindowWidth - 1));
            }

            // Draw Footer after the last tracker
            int newFooterRow = ROW_PROGRESS_START + _activeTrackers.Count;
            DrawFooterAt(newFooterRow);

            // Clear any lines that used to be footer or progress bars
            if (newFooterRow < _lastFooterRow)
            {
                // We moved up, so clear the old lines below us
                for (int r = newFooterRow + 2; r <= _lastFooterRow + 1; r++)
                {
                    Console.SetCursorPosition(0, r);
                    Console.Write(new string(' ', Console.WindowWidth - 1));
                }
            }

            _lastFooterRow = newFooterRow;
        }

        private static void RedrawFooter()
        {
            lock (_consoleLock)
            {
                // Just redraw the footer at current position (to update error msg)
                DrawFooterAt(_lastFooterRow);
            }
        }

        private static void DrawFooterAt(int row)
        {
            Console.SetCursorPosition(0, row);
            Console.WriteLine("--------------------------------------------------------------------------------");
            Console.SetCursorPosition(0, row + 1);
            string safeErr = _lastErrorMsg.Length > 60 ? _lastErrorMsg.Substring(0, 60) : _lastErrorMsg;
            Console.Write($" LAST ERROR: {safeErr}".PadRight(Console.WindowWidth - 1));
        }

        // --- DOWNLOAD HELPERS ---

        private static async Task DownloadFileStandardAsync(string url, string destinationPath, SlotProgressTracker tracker)
        {
            const int BufferSize = 32768;
            using (var request = new HttpRequestMessage(HttpMethod.Get, url))
            {
                request.Headers.TryAddWithoutValidation("User-Agent", "curl/7.68.0");
                using (var response = await _httpClient.SendAsync(request, HttpCompletionOption.ResponseHeadersRead))
                {
                    if (!response.IsSuccessStatusCode) throw new Exception($"HTTP {response.StatusCode}");
                    using (var contentStream = await response.Content.ReadAsStreamAsync())
                    using (var fileStream = new FileStream(destinationPath, FileMode.Create, FileAccess.Write, FileShare.None, BufferSize, true))
                    {
                        var buffer = new byte[BufferSize];
                        int read;
                        long totalRead = 0;
                        var sw = Stopwatch.StartNew();

                        while ((read = await contentStream.ReadAsync(buffer, 0, buffer.Length)) > 0)
                        {
                            await fileStream.WriteAsync(buffer, 0, read);
                            totalRead += read;

                            // Calculate Speed for tracker
                            double speed = totalRead / sw.Elapsed.TotalSeconds;
                            tracker.SetSpeed(speed);
                            tracker.Report(read);
                        }
                    }
                }
            }
        }

        private static async Task DownloadFileChunkedAsync(string url, string destinationPath, long totalSize, int threadCount, SlotProgressTracker tracker)
        {
            using (var fs = new FileStream(destinationPath, FileMode.Create, FileAccess.Write, FileShare.Write)) fs.SetLength(totalSize);

            long partSize = totalSize / threadCount;
            var chunks = new List<(long Start, long End, int Id)>();
            for (int i = 0; i < threadCount; i++)
            {
                long start = i * partSize;
                long end = (i == threadCount - 1) ? totalSize - 1 : (start + partSize - 1);
                chunks.Add((start, end, i));
            }

            long totalReadGlobal = 0;
            var sw = Stopwatch.StartNew();

            await Task.WhenAll(chunks.Select(async chunk =>
            {
                using (var request = new HttpRequestMessage(HttpMethod.Get, url))
                {
                    request.Headers.TryAddWithoutValidation("User-Agent", "curl/7.68.0");
                    request.Headers.Range = new RangeHeaderValue(chunk.Start, chunk.End);
                    using (var response = await _httpClient.SendAsync(request, HttpCompletionOption.ResponseHeadersRead))
                    {
                        if (!response.IsSuccessStatusCode) throw new Exception($"HTTP {response.StatusCode}");
                        using (var remoteStream = await response.Content.ReadAsStreamAsync())
                        using (var fs = new FileStream(destinationPath, FileMode.Open, FileAccess.Write, FileShare.ReadWrite))
                        {
                            fs.Seek(chunk.Start, SeekOrigin.Begin);
                            byte[] buffer = new byte[32768];
                            int read;
                            while ((read = await remoteStream.ReadAsync(buffer, 0, buffer.Length)) > 0)
                            {
                                await fs.WriteAsync(buffer, 0, read);
                                long currentGlobal = Interlocked.Add(ref totalReadGlobal, read);
                                double speed = currentGlobal / sw.Elapsed.TotalSeconds;
                                tracker.SetSpeed(speed);
                                tracker.Report(read);
                            }
                        }
                    }
                }
            }));
        }

        // --- UI UTILS ---

        private static void DrawStaticUiFrame()
        {
            Console.SetCursorPosition(0, 0);
            Console.WriteLine("================================================================================");
            Console.WriteLine($" DOJ Scraper: Adaptive Engine");
            Console.WriteLine($" [{MAX_TOTAL_THREADS} Global Threads] | [Large Files use {LARGE_FILE_COST} Threads]");
            Console.WriteLine("================================================================================");
            Console.SetCursorPosition(0, UI_HEADER_HEIGHT - 1);
            Console.WriteLine("--------------------------------------------------------------------------------");

            // Middle Separator
            Console.SetCursorPosition(0, ROW_DIVIDER);
            Console.WriteLine("--------------------------------------------------------------------------------");
            // Footer is drawn dynamically later
        }

        private static void UpdateGlobalStats(TimeSpan elapsed)
        {
            double totalSeconds = elapsed.TotalSeconds;
            long bytes = Interlocked.Read(ref _totalBytesDownloaded);
            double speed = totalSeconds > 0 ? bytes / totalSeconds : 0;
            int done = _filesDownloaded + _filesFailed;

            lock (_consoleLock)
            {
                Console.SetCursorPosition(0, 4);
                Console.Write($" Files: {done}/{_totalFilesToDownload} (Fail: {_filesFailed})".PadRight(35));
                Console.Write($" Data : {FormatBytes(bytes)}".PadRight(25));

                Console.SetCursorPosition(0, 5);
                Console.Write($" Time : {elapsed:hh\\:mm\\:ss}".PadRight(35));
                Console.Write($" Speed: {FormatBytes((long)speed)}/s".PadRight(25));
            }
        }

        private static void DrawSlotStatus(List<int> slots, string group, string file, string status)
        {
            lock (_consoleLock)
            {
                foreach (var slot in slots)
                {
                    string text = $" [{slot + 1}] {status}: ({group}) {file}";
                    if (text.Length > Console.WindowWidth - 1) text = text.Substring(0, Console.WindowWidth - 1);
                    Console.SetCursorPosition(0, ROW_STATUS_START + slot);
                    Console.Write(text.PadRight(Console.WindowWidth - 1));
                }
            }
        }

        private static void ClearStatusSlots(List<int> slots)
        {
            lock (_consoleLock)
            {
                foreach (var slot in slots)
                {
                    Console.SetCursorPosition(0, ROW_STATUS_START + slot);
                    Console.Write(new string(' ', Console.WindowWidth - 1));
                    Console.SetCursorPosition(0, ROW_STATUS_START + slot);
                    Console.Write($" [{slot + 1}] Idle...");
                }
            }
        }

        private static void LogFailure(DownloadItem item, string code, string error)
        {
            string line = $"[{DateTime.Now}] CODE: {code} | URL: {item.Url} | ERROR: {error}\n";
            lock (_logFileLock) File.AppendAllText(LOG_FILE, line);
        }

        private static async Task<long> GetFileSizeAsync(string url)
        {
            try
            {
                using (var req = new HttpRequestMessage(HttpMethod.Head, url))
                {
                    req.Headers.TryAddWithoutValidation("User-Agent", "curl/7.68.0");
                    using (var resp = await _httpClient.SendAsync(req, HttpCompletionOption.ResponseHeadersRead))
                    {
                        if (resp.IsSuccessStatusCode && resp.Content.Headers.ContentLength.HasValue) return resp.Content.Headers.ContentLength.Value;
                    }
                }
            }
            catch { }
            try
            {
                using (var req = new HttpRequestMessage(HttpMethod.Get, url))
                {
                    req.Headers.TryAddWithoutValidation("User-Agent", "curl/7.68.0");
                    req.Headers.Range = new RangeHeaderValue(0, 0);
                    using (var resp = await _httpClient.SendAsync(req, HttpCompletionOption.ResponseHeadersRead))
                    {
                        if (resp.Content.Headers.ContentRange != null && resp.Content.Headers.ContentRange.Length.HasValue) return resp.Content.Headers.ContentRange.Length.Value;
                    }
                }
            }
            catch { }
            return 0;
        }

        private static string FormatBytes(long bytes)
        {
            string[] sizes = { "B", "KB", "MB", "GB", "TB" };
            double len = bytes;
            int order = 0;
            while (len >= 1024 && order < sizes.Length - 1) { order++; len /= 1024; }
            return $"{len:0.00} {sizes[order]}";
        }

        private static async Task ScrapeAndBuildQueue()
        {
            Console.WriteLine("Scraping index pages...");
            var tasks = new List<Task>();
            tasks.Add(ScrapeCourtRecordsSection());
            tasks.Add(ScrapeStandardSection("https://www.justice.gov/epstein/foia", "Freedom of Information Act (FOIA)"));
            tasks.Add(ScrapeStandardSection("https://www.justice.gov/epstein/doj-disclosures", "DOJ Disclosures"));
            if (tasks.Count > 0) await Task.WhenAll(tasks);
        }

        private static async Task ScrapeStandardSection(string url, string sectionName)
        {
            try
            {
                string html = await _httpClient.GetStringAsync(url);
                ScrapeResult result = ExtractDojLinks(html, url);
                result.Name = sectionName;
                AddToQueue(result);
            }
            catch (Exception ex) { Console.WriteLine($"Error scraping {sectionName}: {ex.Message}"); }
        }

        private static async Task ScrapeCourtRecordsSection()
        {
            string url = "https://www.justice.gov/epstein/court-records";
            try
            {
                string html = await _httpClient.GetStringAsync(url);
                ScrapeResult mainResult = ExtractDojLinks(html, url);
                mainResult.Name = "Court Records";
                var subPageLinks = mainResult.Items.Where(x => x.Url.Contains("/court-records/")).ToList();
                var directFiles = mainResult.Items.Where(x => !x.Url.Contains("/court-records/")).ToList();
                var subPageTasks = subPageLinks.Select(async pageLink =>
                {
                    try
                    {
                        string subHtml = await _httpClient.GetStringAsync(pageLink.Url);
                        var subResult = ExtractDojLinks(subHtml, pageLink.Url);
                        foreach (var item in subResult.Items) item.GroupName = pageLink.GroupName;
                        return subResult.Items;
                    }
                    catch { return new List<DownloadItem>(); }
                });
                var subPageResults = await Task.WhenAll(subPageTasks);
                foreach (var list in subPageResults) directFiles.AddRange(list);
                mainResult.Items = directFiles;
                AddToQueue(mainResult);
            }
            catch (Exception ex) { Console.WriteLine($"Error scraping Court Records: {ex.Message}"); }
        }

        private static void AddToQueue(ScrapeResult result)
        {
            string baseDir = Path.Combine(Environment.CurrentDirectory, "Epstein Files", result.Name);
            if (!Directory.Exists(baseDir)) Directory.CreateDirectory(baseDir);

            int index = 0;
            foreach (var item in result.Items)
            {
                string safeGroupName = SanitizeFilename(item.GroupName);
                string safeSectionName = SanitizeFilename(result.Name);

                string targetDir;

                // --- FIX: PREVENT DUPLICATE NESTING ---
                // If the detected Group Name is the same as the Section Name (e.g., "Court Records" inside "Court Records"),
                // it means these are general files. We put them in the base directory rather than making a subfolder.
                if (string.Equals(safeGroupName, safeSectionName, StringComparison.OrdinalIgnoreCase))
                {
                    targetDir = baseDir;
                }
                else
                {
                    targetDir = Path.Combine(baseDir, safeGroupName);
                }
                // --------------------------------------

                if (!Directory.Exists(targetDir)) Directory.CreateDirectory(targetDir);

                string fName = Path.GetFileName(new Uri(item.Url).LocalPath);
                if (string.IsNullOrWhiteSpace(fName)) fName = $"file_{index}.pdf";

                fName = Uri.UnescapeDataString(fName);

                item.LocalPath = Path.Combine(targetDir, fName);
                item.FileName = fName;
                _masterQueue.Enqueue(item);
                index++;
            }
        }

        public static ScrapeResult ExtractDojLinks(string html, string baseUrl)
        {
            var r = new ScrapeResult();
            var doc = new HtmlDocument();
            doc.LoadHtml(html);

            string title = "Unknown";
            var h1 = doc.DocumentNode.SelectSingleNode("//h1");
            if (h1 != null) title = WebUtility.HtmlDecode(h1.InnerText).Trim();

            // --- FIX START: ROBUST ACCORDION LOGIC ---
            // 1. Find all Accordion Content divs (where the files are).
            // 2. Look backwards to find the immediately preceding Heading (where the Name is).
            // 3. Extract all links from the content div and assign them the Heading's name.

            var accordionContentDivs = doc.DocumentNode.SelectNodes("//div[contains(@class, 'usa-accordion__content')]");

            if (accordionContentDivs != null && accordionContentDivs.Count > 0)
            {
                foreach (var contentDiv in accordionContentDivs)
                {
                    // Walk backwards from the content div to find the associated header
                    var sibling = contentDiv.PreviousSibling;
                    while (sibling != null && (sibling.NodeType == HtmlNodeType.Text || string.IsNullOrWhiteSpace(sibling.Name)))
                    {
                        sibling = sibling.PreviousSibling;
                    }

                    // We expect an H4 with class 'usa-accordion__heading'
                    if (sibling != null && sibling.Name == "h4" && sibling.Attributes["class"] != null && sibling.Attributes["class"].Value.Contains("usa-accordion__heading"))
                    {
                        // The folder name is inside the button within this H4
                        var btn = sibling.SelectSingleNode(".//button");
                        if (btn != null)
                        {
                            string groupName = WebUtility.HtmlDecode(btn.InnerText).Trim();

                            // Now get ALL relevant files inside this specific content div.
                            var links = contentDiv.SelectNodes(".//a");

                            if (links != null)
                            {
                                foreach (var link in links)
                                {
                                    string href = link.GetAttributeValue("href", "");
                                    if (string.IsNullOrWhiteSpace(href)) continue;

                                    string lowerHref = href.ToLowerInvariant();

                                    // FIX: Added check for "/court-records/" to allow sub-page redirects to pass through
                                    if (lowerHref.Contains(".pdf") ||
                                        lowerHref.Contains(".zip") ||
                                        lowerHref.Contains(".mp4") ||
                                        lowerHref.Contains(".wav") ||
                                        lowerHref.Contains(".mp3") ||
                                        lowerHref.Contains(".mov") ||
                                        lowerHref.Contains("/court-records/"))
                                    {
                                        string absoluteUrl = FixUrl(href, baseUrl);
                                        if (absoluteUrl != null)
                                        {
                                            r.Items.Add(new DownloadItem { GroupName = groupName, Url = absoluteUrl });
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                if (r.Items.Count > 0) return r;
            }
            // --- FIX END ---

            // --- LEGACY LOGIC (Maintains support for pages without accordions) ---
            var uls = doc.DocumentNode.SelectNodes("//ul");
            if (uls == null) return r;

            foreach (var ul in uls)
            {
                var files = ul.SelectNodes(".//a[contains(@href, '.pdf') or contains(@href, '.zip') or contains(@href, '.mp4')]");

                if (files == null)
                {
                    // Handle sub-page navigation (e.g. Court Records year links)
                    var subpages = ul.SelectNodes(".//a[contains(@href, '/court-records/')]");
                    if (subpages != null)
                    {
                        foreach (var link in subpages)
                        {
                            string rawHref = link.GetAttributeValue("href", "");
                            string absoluteUrl = FixUrl(rawHref, baseUrl);
                            if (absoluteUrl != null) r.Items.Add(new DownloadItem { GroupName = link.InnerText.Trim(), Url = absoluteUrl });
                        }
                    }
                    continue;
                }

                string group = title;
                var prev = ul.PreviousSibling;
                while (prev != null && prev.NodeType == HtmlNodeType.Text) prev = prev.PreviousSibling;

                if (prev != null && (prev.Name.StartsWith("h") || prev.Name == "p"))
                {
                    group = WebUtility.HtmlDecode(prev.InnerText).Trim();
                }

                foreach (var f in files)
                {
                    string rawHref = f.GetAttributeValue("href", "");
                    string absoluteUrl = FixUrl(rawHref, baseUrl);
                    if (absoluteUrl != null) r.Items.Add(new DownloadItem { GroupName = group, Url = absoluteUrl });
                }
            }
            return r;
        }

        private static string FixUrl(string href, string baseUrl)
        {
            if (string.IsNullOrWhiteSpace(href)) return null;
            href = WebUtility.HtmlDecode(href).Trim();
            if (href.StartsWith("javascript:", StringComparison.OrdinalIgnoreCase)) return null;
            if (href.StartsWith("mailto:", StringComparison.OrdinalIgnoreCase)) return null;
            href = href.Replace(" ", "%20").Replace("#", "%23");
            try
            {
                Uri baseUri = new Uri(baseUrl);
                Uri absolute = new Uri(baseUri, href);
                if (!absolute.OriginalString.StartsWith("https://www.justice.gov/", StringComparison.OrdinalIgnoreCase)) return null;
                return absolute.ToString();
            }
            catch { return null; }
        }

        private static string SanitizeFilename(string name)
        {
            if (string.IsNullOrEmpty(name)) return "Unknown";
            string invalid = new string(Path.GetInvalidFileNameChars()) + new string(Path.GetInvalidPathChars());
            foreach (char c in invalid) name = name.Replace(c, '_');
            return name.Length > 50 ? name.Substring(0, 50).Trim() : name.Trim();
        }
    }
}