#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>

using Table = std::uint16_t;
constexpr int pointCount = 5;
constexpr int sampleCount = 15;
constexpr int cap = 6;
constexpr Table all = (1 << sampleCount) - 1;
constexpr int unknown = cap + 1;

std::array<Table, pointCount + cap> wires{};
std::array<int, all + 1> minimum;

void consider(Table value, int wireCount);
void search(int wireCount) {
    for (int a = 0; a < wireCount; ++a) {
        consider(wires[a] ^ all, wireCount);
        for (int b = 0; b < a; ++b) {
            consider(wires[a] & wires[b], wireCount);
            consider(wires[a] | wires[b], wireCount);
        }
    }
}

void consider(Table value, int wireCount) {
    const int cost = wireCount - pointCount + 1;
    minimum[value] = std::min(minimum[value], cost);
    if (cost == cap || value == 0 || value == all) {
        return;
    }
    const auto end = wires.begin() + wireCount;
    if (std::find(wires.begin(), end, value) == end) {
        wires[wireCount] = value;
        search(wireCount + 1);
    }
}

int main() {
    minimum.fill(unknown);
    int sample = 0;
    Table target = 0;
    for (int a = 0; a < pointCount; ++a) {
        for (int b = a; b < pointCount; ++b, ++sample) {
            const Table bit = 1 << sample;
            wires[a] |= bit;
            wires[b] |= bit;
            if ((283359u >> (pointCount * a + b)) & 1) {
                target |= bit;
            }
        }
    }
    for (int i = 0; i < pointCount; ++i) {
        minimum[wires[i]] = 0;
    }
    search(pointCount);
    assert(minimum[target] == unknown);

    // List only the nonconstant tables, including the five projections.
    for (int value = 1; value < all; ++value) {
        if (minimum[value] != unknown) {
            std::cout << value << ' ' << minimum[value] << '\n';
        }
    }
}
