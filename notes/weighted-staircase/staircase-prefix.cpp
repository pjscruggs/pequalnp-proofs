#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using Table = std::uint16_t;
constexpr Table care = (1 << 9) - 1;
constexpr Table target = (1 << 5) | (1 << 7) | (1 << 8);

bool reaches(std::vector<Table>& signals, int remaining, bool signed_basis) {
    if (std::find(signals.begin(), signals.end(), target) != signals.end()) {
        return true;
    }
    if (remaining == 0) {
        return false;
    }
    const auto count = signals.size();
    const auto add = [&](Table value) {
        if (value == 0 || value == care ||
            std::find(signals.begin(), signals.end(), value) != signals.end()) {
            return false;
        }
        signals.push_back(value);
        const bool found = reaches(signals, remaining - 1, signed_basis);
        signals.pop_back();
        return found;
    };
    for (std::size_t a = 0; a < count; ++a) {
        if (signed_basis && add(signals[a] ^ care)) {
            return true;
        }
        for (std::size_t b = 0; b < a; ++b) {
            if (add(signals[a] & signals[b]) || add(signals[a] | signals[b])) {
                return true;
            }
        }
    }
    return false;
}

std::vector<Table> encode(int row_default, int col_default) {
    std::vector<Table> signals;
    for (int shore = 0; shore < 2; ++shore) {
        for (int type = 0; type < 3; ++type) {
            if (type == (shore == 0 ? row_default : col_default)) {
                continue;
            }
            Table stripe = 0;
            for (int cell = 0; cell < 9; ++cell) {
                if (type == (shore == 0 ? cell / 3 : cell % 3)) {
                    stripe |= 1 << cell;
                }
            }
            signals.push_back(stripe);
        }
    }
    return signals;
}

int main() {
    for (bool signed_basis : {false, true}) {
        const int last = signed_basis ? 2 : 0;
        for (int row = -1; row <= last; ++row) {
            for (int col = -1; col <= last; ++col) {
                auto signals = encode(row, col);
                int minimum = 0;
                while (minimum <= 5 && !reaches(signals, minimum, signed_basis)) {
                    ++minimum;
                }
                std::cout << signed_basis << ' ' << row << ' ' << col << ' ' << minimum << '\n';
            }
        }
    }
}
