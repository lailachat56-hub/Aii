#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <cmath>
#include <algorithm>
#include <iomanip>
#include <string>
#include <chrono>
#include <stdexcept>
using namespace std;

// يمثل موضع النملة داخل المتاهة باستخدام رقم الصف والعمود (داخليًا يبدأ العد من صفر).
struct Position {
    int row, col;
    // مقارنة موضعين لمعرفة هل يشيران إلى الخلية نفسها.
    bool operator==(const Position& other) const {
        return row == other.row && col == other.col;
    }
};

// يجمع نتيجة عملية البحث: الوصول للهدف والتكلفة وإحصاءات الأداء والمسار النهائي.
struct SearchResult {
    bool found = false;
    int pathCost = -1;
    int expanded = 0;
    int generated = 0;
    size_t maxFrontier = 0;
    double timeMicros = 0.0;
    vector<Position> path;
};

// الصنف الرئيسي المسؤول عن تخزين المتاهة وتشغيل خوارزميات البحث وتحليل النتائج.
class MazeSolver {
private:
    // تخزين صفوف المتاهة وأبعادها وموقع الطعام ونقاط البداية الموجودة في الملف.
    vector<string> maze;
    int rows = 0, cols = 0;
    Position goal = {-1, -1};
    vector<Position> fileStarts;

    // عنصر داخل قائمة الانتظار: الأولوية وترتيب الإدخال والتكلفة الفعلية والموضع.
    struct Entry {
        double priority;
        int serial;
        int g;
        Position pos;
    };
    // ترتيب قائمة الأولوية: الأقل في f أولاً، ثم الصف، ثم العمود، ثم الأسبق إدخالاً.
    struct Compare {
        bool operator()(const Entry& a, const Entry& b) const {
            if (fabs(a.priority - b.priority) > 1e-9) return a.priority > b.priority;
            if (a.pos.row != b.pos.row) return a.pos.row > b.pos.row;
            if (a.pos.col != b.pos.col) return a.pos.col > b.pos.col;
            return a.serial > b.serial;
        }
    };
    // التحقق من أن الموضع داخل حدود المتاهة.
    bool inside(Position p) const {
        return p.row >= 0 && p.row < rows && p.col >= 0 && p.col < cols;
    }
    // يسمح بالمرور في الخلايا الفارغة والمغمورة بالمياه، ويمنع الجدران (#).
    bool passable(Position p) const {
        return inside(p) && maze[p.row][p.col] != '#';
    }
    // حساب المسافة التخمينية إلى الهدف: مانهاتن أو إقليدية حسب الاختيار.
    double heuristic(Position p, bool manhattan) const {
        int dr = abs(p.row - goal.row);
        int dc = abs(p.col - goal.col);
        if (manhattan) return double(dr + dc);
        return sqrt(double(dr * dr + dc * dc));
    }
    // فحص سلامة المتاهة وتحديد الهدف وتحويل رمز البداية S إلى خلية عادية.
    void validateAndPrepare() {
        if (maze.empty()) throw runtime_error("Maze is empty");
        rows = (int)maze.size();
        cols = (int)maze[0].size();
        int foodCount = 0;
        for (int r = 0; r < rows; ++r) {
            if ((int)maze[r].size() != cols)
                throw runtime_error("All maze rows must have equal length");
            for (int c = 0; c < cols; ++c) {
                char ch = maze[r][c];
                if (ch == 'X') { goal = {r, c}; ++foodCount; }
                else if (ch == 'S') { fileStarts.push_back({r, c}); maze[r][c] = '.'; }
                else if (ch != '.' && ch != '~' && ch != '#')
                    throw runtime_error(string("Unknown maze symbol: ") + ch);
            }
        }
        if (foodCount != 1) throw runtime_error("Maze must contain exactly one X goal");
    }
public:
    // المُنشئ: يستقبل المتاهة ويجري فحصًا أوليًا لها.
    explicit MazeSolver(const vector<string>& grid) : maze(grid) { validateAndPrepare(); }
    // قراءة متاهة اختيارية من ملف نصي مع تجاهل الفراغات بين الرموز.
    static vector<string> loadFromFile(const string& path) {
        ifstream in(path);
        if (!in) throw runtime_error("Cannot open file: " + path);
        vector<string> grid;
        string line;
        while (getline(in, line)) {
            string clean;
            for (char ch : line)
                if (ch != ' ' && ch != '\r' && ch != '\t') clean += ch;
            if (!clean.empty()) grid.push_back(clean);
        }
        return grid;
    }
    // إرجاع مواقع البداية المحددة برمز S في ملف المتاهة.
    const vector<Position>& startsFromMaze() const { return fileStarts; }
    // التأكد من صلاحية نقطة البداية وأنها ليست جدارًا أو خارج الحدود.
    bool validStart(Position p) const { return passable(p); }
    // طباعة المتاهة على الشاشة وإظهار موضع البداية المختار برمز S.
    void printMaze(Position start) const {
        cout << "Maze (. empty, ~ flooded, # wall, X goal, S start):\n";
        for (int r = 0; r < rows; ++r) {
            for (int c = 0; c < cols; ++c) {
                char cell = maze[r][c];
                if (start.row == r && start.col == c && !(start == goal)) cell = 'S';
                cout << cell << ' ';
            }
            cout << '\n';
        }
    }
    // استخدام BFS من الهدف لحساب أقل عدد حركات حقيقي لكل خلية قابلة للوصول.
    vector<vector<int>> distancesFromGoal() const {
        vector<vector<int>> dist(rows, vector<int>(cols, -1));
        queue<Position> q;
        dist[goal.row][goal.col] = 0;
        q.push(goal);
        const int dr[4] = {-1, 0, 1, 0};
        const int dc[4] = {0, 1, 0, -1};
        while (!q.empty()) {
            Position p = q.front(); q.pop();
            for (int i = 0; i < 4; ++i) {
                Position n = {p.row + dr[i], p.col + dc[i]};
                if (passable(n) && dist[n.row][n.col] == -1) {
                    dist[n.row][n.col] = dist[p.row][p.col] + 1;
                    q.push(n);
                }
            }
        }
        return dist;
    }
    // تحليل الدالتين التخمينيّتين ومقارنتهما بالتكلفة الحقيقية والتحقق من المقبولية والاتساق.
    void printHeuristicReport() const {
        auto dist = distancesFromGoal();
        int cells = 0, h1Bad = 0, h2Bad = 0, h2Greater = 0, h1Cons = 0, h2Cons = 0;
        double sumH1 = 0, sumH2 = 0, sumStar = 0;
        const int dr[4] = {-1, 0, 1, 0};
        const int dc[4] = {0, 1, 0, -1};
        for (int r = 0; r < rows; ++r) {
            for (int c = 0; c < cols; ++c) {
                Position p = {r, c};
                if (!passable(p) || dist[r][c] < 0) continue;
                ++cells;
                double h1 = heuristic(p, false), h2 = heuristic(p, true);
                int star = dist[r][c];
                sumH1 += h1; sumH2 += h2; sumStar += star;
                if (h1 > star + 1e-9) ++h1Bad;
                if (h2 > star + 1e-9) ++h2Bad;
                if (h2 > h1 + 1e-9) ++h2Greater;
                for (int i = 0; i < 4; ++i) {
                    Position n = {r + dr[i], c + dc[i]};
                    if (!passable(n) || dist[n.row][n.col] < 0) continue;
                    if (fabs(heuristic(p, false) - heuristic(n, false)) > 1 + 1e-9) ++h1Cons;
                    if (fabs(heuristic(p, true) - heuristic(n, true)) > 1 + 1e-9) ++h2Cons;
                }
            }
        }
        cout << "\n================ HEURISTIC ANALYSIS ================\n";
        cout << "Checked cells: " << cells << '\n';
        cout << fixed << setprecision(2);
        if (cells > 0) {
            cout << "Average h1 (Euclidean) = " << sumH1 / cells << '\n';
            cout << "Average h2 (Manhattan) = " << sumH2 / cells << '\n';
            cout << "Average h* (true cost) = " << sumStar / cells << '\n';
        }
        cout << "h1 admissible? " << (h1Bad == 0 ? "Yes" : "No") << " (violations: " << h1Bad << ")\n";
        cout << "h2 admissible? " << (h2Bad == 0 ? "Yes" : "No") << " (violations: " << h2Bad << ")\n";
        cout << "h1 consistent? " << (h1Cons == 0 ? "Yes" : "No") << " (violations: " << h1Cons << ")\n";
        cout << "h2 consistent? " << (h2Cons == 0 ? "Yes" : "No") << " (violations: " << h2Cons << ")\n";
        cout << "Cells where h2 > h1: " << h2Greater << " of " << cells << '\n';
        cout << "(h2 >= h1, so Manhattan dominates Euclidean here.)\n";
        cout << defaultfloat;
    }
    // تنفيذ Greedy أو A* حسب useAStar، واختيار مانهاتن أو إقليدية حسب manhattan.
    SearchResult search(Position start, bool useAStar, bool manhattan) const {
        SearchResult result;
        if (!validStart(start)) return result;
        auto t0 = chrono::high_resolution_clock::now();
        const int INF = 1000000000;
        // best: أفضل تكلفة معروفة؛ closed: العقد التي عولجت؛ parent: لاستعادة المسار.
        vector<vector<int>> best(rows, vector<int>(cols, INF));
        vector<vector<bool>> closed(rows, vector<bool>(cols, false));
        vector<vector<Position>> parent(rows, vector<Position>(cols, Position{-1, -1}));
        // قائمة العقد المرشحة للزيارة مرتبة وفق الأولوية.
        priority_queue<Entry, vector<Entry>, Compare> frontier;
        int serial = 0;
        best[start.row][start.col] = 0;
        frontier.push({heuristic(start, manhattan), serial++, 0, start});
        result.generated = 1;
        result.maxFrontier = 1;
        const int dr[4] = {-1, 0, 1, 0};
        const int dc[4] = {0, 1, 0, -1};
        // تكرار اختيار العقدة ذات الأولوية الأفضل حتى الوصول للهدف أو نفاد العقد.
        while (!frontier.empty()) {
            Entry current = frontier.top(); frontier.pop();
            Position p = current.pos;
            // تجاهل الإدخالات القديمة أو العقد المغلقة حتى لا نكرر معالجة الحالة نفسها.
            if (current.g != best[p.row][p.col] || closed[p.row][p.col]) continue;
            closed[p.row][p.col] = true;
            ++result.expanded;
            // عند الوصول للطعام، نستعيد المسار من الهدف إلى البداية ثم نعكسه.
            if (p == goal) {
                result.found = true;
                result.pathCost = current.g;
                Position q = p;
                while (!(q == start)) {
                    result.path.push_back(q);
                    q = parent[q.row][q.col];
                }
                result.path.push_back(start);
                reverse(result.path.begin(), result.path.end());
                break;
            }
            for (int i = 0; i < 4; ++i) {
                Position next = {p.row + dr[i], p.col + dc[i]};
                if (!passable(next)) continue;
                int candidateG = current.g + 1;
                // A* تقبل مسارًا أقل تكلفة وتسمح بإعادة فتح العقدة؛ Greedy تقبل الزيارة الأولى فقط.
                bool accept = useAStar ? (candidateG < best[next.row][next.col])
                                       : (best[next.row][next.col] == INF);
                if (!accept) continue;
                best[next.row][next.col] = candidateG;
                parent[next.row][next.col] = p;
                closed[next.row][next.col] = false;
                // حساب الأولوية: في A* نضيف g إلى h، وفي Greedy نستخدم h وحدها.
                double priority = (useAStar ? candidateG : 0) + heuristic(next, manhattan);
                frontier.push({priority, serial++, candidateG, next});
                ++result.generated;
                result.maxFrontier = max(result.maxFrontier, frontier.size());
            }
        }
        auto t1 = chrono::high_resolution_clock::now();
        // حساب زمن التنفيذ بالميكروثانية لأغراض المقارنة التجريبية.
        result.timeMicros = chrono::duration<double, micro>(t1 - t0).count();
        return result;
    }
    // اختبار نقطة بداية واحدة باستخدام الخوارزميات الأربع وطباعة النتائج وحفظها في CSV.
    void runCase(Position start, ofstream* csv) const {
        cout << "\n======================================================\n";
        cout << "Start (row,column) = (" << start.row + 1 << ',' << start.col + 1 << ")\n";
        if (!validStart(start)) {
            cout << "Invalid start: wall or outside maze.\n";
            return;
        }
        printMaze(start);
        auto dist = distancesFromGoal();
        // تكلفة BFS المرجعية تُستخدم للتحقق من أن المسار الناتج أمثل.
        int optimal = dist[start.row][start.col];
        cout << "True optimal cost (BFS) = " << (optimal < 0 ? string("Unreachable") : to_string(optimal)) << '\n';
        const string names[4] = {"Greedy + Euclidean", "Greedy + Manhattan",
                                 "A* + Euclidean", "A* + Manhattan"};
        cout << left << setw(22) << "Algorithm" << setw(7) << "Found" << setw(7) << "Cost"
             << setw(9) << "Optimal?" << setw(9) << "Expanded" << setw(10) << "Generated"
             << setw(10) << "MaxFront" << "Time(us)\n";
        // تشغيل Greedy مع الدالتين، ثم A* مع الدالتين، بالترتيب نفسه.
        for (int i = 0; i < 4; ++i) {
            SearchResult r = search(start, i >= 2, i % 2 == 1);
            bool isOptimal = r.found && r.pathCost == optimal;
            cout << left << setw(22) << names[i] << setw(7) << (r.found ? "Yes" : "No")
                 << setw(7) << (r.found ? to_string(r.pathCost) : "N/A")
                 << setw(9) << (r.found ? (isOptimal ? "Yes" : "No") : "N/A")
                 << setw(9) << r.expanded << setw(10) << r.generated
                 << setw(10) << r.maxFrontier << fixed << setprecision(1) << r.timeMicros << '\n';
            cout << defaultfloat;
            cout << "Path: ";
            if (!r.found) cout << "No path";
            else for (size_t j = 0; j < r.path.size(); ++j) {
                if (j) cout << " -> ";
                cout << '(' << r.path[j].row + 1 << ',' << r.path[j].col + 1 << ')';
            }
            cout << '\n';
            // تسجيل نتائج هذه التجربة في ملف النتائج لتحليلها في التقرير.
            if (csv && csv->is_open()) {
                *csv << start.row + 1 << ':' << start.col + 1 << ',' << names[i] << ','
                     << (r.found ? 1 : 0) << ',' << r.pathCost << ',' << optimal << ','
                     << r.expanded << ',' << r.generated << ',' << r.maxFrontier << ','
                     << r.timeMicros << '\n';
            }
        }
    }
};

// نقطة بدء البرنامج: تجهيز المتاهة وتشغيل الاختبارات وعرض التقرير والسماح بإدخال يدوي.
int main(int argc, char* argv[]) {
    try {
        // المتاهة الافتراضية المعتمدة: X الطعام، # جدار، ~ ماء قابل للعبور، . خلية فارغة.
        vector<string> grid = {"....X", "#~###", ".~...", "#~#.#", ".~..."};
        bool customMaze = false;
        // عند تمرير اسم ملف من سطر الأوامر نقرأ المتاهة منه بدل المتاهة الافتراضية.
        if (argc > 1) {
            grid = MazeSolver::loadFromFile(argv[1]);
            customMaze = true;
        }
        MazeSolver solver(grid);
        cout << "CS456 Assignment 3 - Phase II: Ant in a Flooded Maze\n";
        cout << "Coordinates are 1-based (row,column). Flooded cells are passable. Four moves.\n";
        vector<Position> starts = solver.startsFromMaze();
        // إن لم توجد نقطة S في الملف، نستخدم خمس نقاط اختبار محددة مسبقًا.
        if (starts.empty()) {
            if (!customMaze) starts = {{4,0}, {2,0}, {2,2}, {4,2}, {4,4}};
            else cout << "No S starts in the file; use manual input below.\n";
        }
        // إنشاء ملف CSV لتسجيل بيانات جميع التجارب.
        ofstream csv("results.csv");
        csv << "start,algorithm,found,cost,optimal_cost,expanded,generated,max_frontier,time_us\n";
        for (Position p : starts) solver.runCase(p, &csv);
        // عرض التحليل النهائي للدالتين: Admissibility وConsistency والمقارنة بينهما.
        solver.printHeuristicReport();
        cout << "\nCustom start: enter row and column (1-based), or 0 0 to quit: ";
        int r, c;
        // تكرار التجارب اليدوية حتى يُدخل المستخدم 0 0 لإنهاء البرنامج.
        while (cin >> r >> c && (r != 0 || c != 0)) {
            solver.runCase({r - 1, c - 1}, &csv);
            cout << "\nAnother start (0 0 to quit): ";
        }
        cout << "\nResults saved to results.csv\n";
    } catch (const exception& e) {
        // إظهار رسالة واضحة عند حدوث خطأ في الملف أو بيانات المتاهة.
        cerr << "Error: " << e.what() << '\n';
        return 1;
    }
    return 0;
}
