// Построение выпуклой оболочки в 3D методом заворачивания подарка

#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>
#include <queue>
#include <set>
#include <unordered_set>

struct Point {
    int x, y, z;
    Point() : x(0), y(0), z(0) {};
    Point(int _x, int _y, int _z) : x(_x), y(_y), z(_z) {};
    Point(const Point& another) : x(another.x), y(another.y), z(another.z) {};
};

class Vector {
private:
    double x, y, z;
public:
    Vector() : x(0), y(0), z(0) {};
    Vector(double _x, double _y, double _z) : x(_x), y(_y), z(_z) {};
    Vector(const Vector& another) : x(another.x), y(another.y), z(another.z) {};
    Vector(const Point& start, const Point& end) {
        x = end.x - start.x;
        y = end.y - start.y;
        z = end.z - start.z;
    }

    double length() const {
        return sqrt(static_cast<double>(x*x + y*y + z*z));
    }
    friend Vector vectorProd(const Vector&, const Vector&);
    friend double scalarProd(const Vector&, const Vector&);
};

// Векторное произведение
Vector vectorProd(const Vector& a, const Vector& b) {
    double x = a.y * b.z - a.z * b.y;
    double y = -a.x * b.z + a.z * b.x;
    double z = a.x * b.y - a.y * b.x;
    return Vector(x, y, z);
}

// Скалярное произведение
double scalarProd(const Vector& a, const Vector& b) {
    return (static_cast<double>(a.x * b.x + a.y * b.y + a.z * b.z));
}

// Структура грани выпуклой оболочки
struct Face {
    int first, second, third; // Номера точек в некотором массиве точек
    Face(int _f, int _s, int _t) : first(_f), second(_s), third(_t) {
        while (!(first < second && first < third)) {
            std::swap(first, second);
            std::swap(second, third);
        }
    }
};

// Компаратор для граней (лексикографический порядок)
struct face_cmp {
    bool operator()(const Face& f1, const Face& f2) const {
        if (f1.first != f2.first) return f1.first < f2.first;
        if (f1.second != f2.second) return f1.second < f2.second;
        return f1.third < f2.third;
    }
};

// Структура ребра выпуклой грани
struct Edge {
    int first, second;
    // Указатель на грань, ребром которой является данное
    const std::set<Face, face_cmp>::iterator face; 
    Edge(int _f, int _s, const std::set<Face, face_cmp>::iterator _face) : 
        first(_f), second(_s), face(_face) {};
};

// Хэш для пары
class hash_pair {
public:
    auto operator()(const std::pair<int, int>& p) const {
        return std::hash<int>()(p.first) + std::hash<int>()(p.second);
    }
};

// Строит выпуклую оболочку
std::set<Face, face_cmp> build_convex_hull(const std::vector<Point> point_set) {
    
    // Поиск первой точки (с мин. z)
    int p0 = 0;
    for (int i = 1; i < point_set.size(); ++i) {
        if (point_set[i].z < point_set[p0].z) {
            p0 = i;
        }
    }

    // Поиск второй точки (угол м-у плоскостью Oxy и ребром p0p1 минимален)
    int p1 = 0;
    if (p1 == p0) {
        p1 = 1;
    }
    double tan = static_cast<double>(point_set[p1].z - point_set[p0].z) /
       static_cast<double>(sqrt(pow(point_set[p1].x - point_set[p0].x, 2) + pow(point_set[p1].y - point_set[p0].y, 2)));
    for (int i = 0; i < point_set.size(); ++i) {
        if (i == p0) continue;
        double current_tan = static_cast<double>(point_set[i].z - point_set[p0].z) /
            static_cast<double>(sqrt(pow(point_set[i].x - point_set[p0].x, 2) + pow(point_set[i].y - point_set[p0].y, 2)));
        if (current_tan < tan) {
            p1 = i;
            tan = current_tan;
        }
    }

    // Итоговое множество граней
    std::set<Face, face_cmp> hull_faces;
    // Очередь "свободных" (только с одной гранью) ребер
    std::queue<Edge> free_edges;
    // Ищем третью точку
    int p2;
    bool found_face = false;
    for (int i = 0; !found_face; ++i) {
        if (i == p0 || i == p1) continue;
        Vector curr_face_normal = vectorProd(Vector(point_set[p0], point_set[p1]), 
            Vector(point_set[p0], point_set[i]));
        bool all_points_on_one_side = true;
        int j = 0;
        while (j == i || j == p0 || j == p1) {
            ++j;
        }
        int prod_sign = (scalarProd(curr_face_normal, Vector(point_set[p0], point_set[j])) >= 0) ? 1 : -1;
        for (++j; all_points_on_one_side && j < point_set.size(); ++j) {
            if (j == i || j == p0 || j == p1) continue;
            all_points_on_one_side = all_points_on_one_side && scalarProd(curr_face_normal, 
                Vector(point_set[p0], point_set[j])) * prod_sign >= 0;
        }
        if (all_points_on_one_side) {
            found_face = true;
            p2 = i;
            // Грань добавляем сразу с правильной ориентацией (с внешней к оболчке нормалью)
            if (prod_sign > 0) {
                Face first_face(p0, p2, p1);
                const std::set<Face, face_cmp>::iterator it = hull_faces.insert(first_face).first;
                free_edges.push(Edge(p0, p2, it));
                free_edges.push(Edge(p2, p1, it));
                free_edges.push(Edge(p1, p0, it));
            } else {
                Face first_face(p0, p1, p2);
                const std::set<Face, face_cmp>::iterator it = hull_faces.insert(first_face).first;
                free_edges.push(Edge(p0, p1, it));
                free_edges.push(Edge(p1, p2, it));
                free_edges.push(Edge(p2, p0, it));
            }
        }
    }

    // Хэш-таблица в которой лежат ребра, которые лежат (или лежали) в очереди
    std::unordered_set<std::pair<int, int>, hash_pair> edgeUsed;
    edgeUsed.insert({p0, p1});
    edgeUsed.insert({p1, p2});
    edgeUsed.insert({p2, p0});

    //Добавляем по грани к каждому ребру из очереди
    while (!free_edges.empty()) {
        Edge e = free_edges.front();
        free_edges.pop();
        p0 = e.face->first;
        p1 = e.face->second;
        p2 = e.face->third;
        Vector face_normal = vectorProd(Vector(point_set[p0], point_set[p2]),
            Vector(point_set[p0], point_set[p1]));
        double maxCos = -1;
        int p;
        for (int i = 0; i < point_set.size(); ++i) {
            if (i == p0 || i == p1 || i == p2) {
                continue;
            }
            Vector current_normal = vectorProd(Vector(point_set[e.first], point_set[e.second]),
                Vector(point_set[e.first], point_set[i]));
            double cos = static_cast<double>(scalarProd(face_normal, current_normal)) /
                static_cast<double>(face_normal.length() * current_normal.length());
            if (cos > maxCos) {
                maxCos = cos;
                p = i;
            }
        }
        Face inserted_face = Face(e.first, p, e.second);
        // Указатель на вставленную грань в set
        auto it = hull_faces.insert(inserted_face).first;
        // Каждое ребро должно быть в очереди только один раз
        if (edgeUsed.find({ e.first, p }) == edgeUsed.end() && edgeUsed.find({ p, e.first }) == edgeUsed.end()) {
            free_edges.push(Edge(e.first, p, it));
            edgeUsed.insert({ e.first, p });
        }
        if (edgeUsed.find({e.second, p}) == edgeUsed.end() && edgeUsed.find({ p, e.second }) == edgeUsed.end()) {
            free_edges.push(Edge(p, e.second, it));
            edgeUsed.insert({ p, e.second });
        }
        
    }
    return hull_faces;
}

int main() {
    int m, n;
    std::cin >> m;
    for (int i = 0; i < m; ++i) {
        std::cin >> n;
        std::vector<Point> point_set(n);
        for (int j = 0; j < n; ++j) {
            std::cin >> point_set[j].x >> point_set[j].y >> point_set[j].z;
        }
        std::set<Face, face_cmp> ch = build_convex_hull(point_set);
        std::cout << ch.size() << std::endl;
        for (const Face& f : ch) {
            std::cout << "3 " << f.first << " " << f.second << " " << f.third << std::endl;
        }
    }
    return 0;
}