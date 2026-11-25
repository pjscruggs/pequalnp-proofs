// c++ -O3 -std=c++17 rectangle_atlas.cpp -o rectangle_atlas
// Usage: rectangle_atlas 4 or rectangle_atlas 5. Table is on standard output.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using Mask = uint32_t;
using Class = uint16_t;
constexpr Class unseen = UINT16_MAX;

struct Orbit {
    Mask graph;
    unsigned size;
    unsigned upper;
};

int main(int argc, char** argv) {
    int n = argc == 2 ? std::atoi(argv[1]) : 0;
    if (n != 4 && n != 5) return 2;
    const unsigned sides = 1u << n, labels = 1u << (n * n);
    const Mask full = labels - 1;
    std::vector<Class> index(labels, unseen);
    std::vector<Orbit> classes;
    std::vector<int> perm(n);
    std::iota(perm.begin(), perm.end(), 0);
    std::vector<std::vector<Mask>> column_maps;
    do {
        std::vector<Mask> map(sides);
        for (Mask x = 0; x < sides; ++x)
            for (int i = 0; i < n; ++i)
                if ((x >> i) & 1) map[x] |= 1u << perm[i];
        column_maps.push_back(map);
    } while (std::next_permutation(perm.begin(), perm.end()));
    for (Mask graph = 0; graph < labels; ++graph) {
        if (index[graph] != unseen) continue;
        if (classes.size() >= unseen) throw std::overflow_error("class ID");
        Class id = static_cast<Class>(classes.size());
        unsigned size = 0;
        Mask transpose = 0;
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                transpose |= ((graph >> (i*n+j)) & 1u) << (j*n+i);
        for (Mask base : {graph, transpose}) {
            for (const auto& col : column_maps) {
                std::vector<Mask> rows(n);
                for (int i = 0; i < n; ++i) rows[i] = col[(base >> (i*n)) & (sides-1)];
                std::sort(rows.begin(), rows.end());
                do {
                    Mask member = 0;
                    for (int i = 0; i < n; ++i) member |= rows[i] << (i*n);
                    if (index[member] == unseen) {
                        index[member] = id;
                        ++size;
                    }
                } while (std::next_permutation(rows.begin(), rows.end()));
            }
        }
        classes.push_back({graph, size, static_cast<unsigned>(n-1)});
    }
    std::vector<Mask> rects{0}, two;
    for (Mask rows = 1; rows < sides; ++rows)
        for (Mask cols = 1; cols < sides; ++cols) {
            Mask rect = 0;
            for (int r = 0; r < n; ++r)
                if ((rows >> r) & 1) rect |= cols << (r*n);
            rects.push_back(rect);
        }
    auto mark = [&](Mask zeroes, unsigned k) {
        auto& upper = classes[index[full ^ zeroes]].upper;
        upper = std::min(upper, k);
    };
    for (Mask r : rects) mark(r, 0);
    for (Mask r : rects) for (Mask s : rects) two.push_back(r | s);
    std::sort(two.begin(), two.end());
    two.erase(std::unique(two.begin(), two.end()), two.end());
    for (Mask h : two) mark(h, 1);
    // Fix the first factor up to symmetry. The second ranges over all labels.
    for (const auto& orbit : classes) {
        if (orbit.upper > 1) continue;
        Mask h = full ^ orbit.graph;
        for (Mask r : rects) mark(h | r, 2);
        for (Mask k : two) mark(h & k, 2);
    }
    // Each operation here is a constructive upper bound at cost three.
    // For n=5 any remaining graph has cost 3 or 4 by the five-row cover.
    if (n == 5) {
        for (const auto& orbit : classes) {
            if (orbit.upper > 2) continue;
            Mask h = full ^ orbit.graph;
            for (Mask r : rects) mark(h | r, 3);
            for (Mask k : two) mark(h & k, 3);
        }
    }
    for (const auto& o : classes)
        std::cout << std::hex << o.graph << std::dec << ' ' << o.size << ' ' << o.upper << '\n';
}
