// Enumerate ordered point paths with no chord on any selected secant.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using Mask = std::uint32_t;
constexpr int max_side = 31;
int n, order, modulus;
Mask all_points;
std::array<Mask, max_side> line{};
int join[max_side][max_side], weight[2][max_side][max_side];
std::array<std::uint64_t, max_side+1> count{};
std::array<std::uint64_t, 4> misses{};

int delta(int k, int a, int b, int j) {
    return weight[k][a][j] - weight[k][b][j];
}

void visit(int root, int second, int last, Mask points, Mask forbidden, int w0, int w1) {
    // A secant from last to root closes an induced cycle precisely when it contains
    // no intermediate point. Root is the least point and second < last fixes orientation.
    int closing = join[last][root];
    if (second < last && std::popcount(points & line[closing]) == 2) {
        int a = w0 + delta(0, last, root, closing);
        int b = w1 + delta(1, last, root, closing);
        ++count[std::popcount(points)];
        ++misses[(a % order == 0) + 2 * (b % order == 0)];
    }
    for (Mask options = all_points & ~forbidden; options; options &= options - 1) {
        int v = std::countr_zero(options), j = join[last][v];
        if ((points & line[j]) != (1u << last)) continue;
        visit(root, second, v, points | (1u << v), forbidden | line[j],
              w0 + delta(0, last, v, j), w1 + delta(1, last, v, j));
    }
}

int gf4(int a, int b) {
    int value = ((b & 1) ? a : 0) ^ ((b & 2) ? a << 1 : 0);
    return value & 4 ? value ^ 7 : value;
}

bool check(int q, int multiplicative_order, int prime_modulus) {
    n = q*q + q + 1;
    order = multiplicative_order;
    modulus = prime_modulus;
    all_points = (1u << n) - 1;
    line.fill(0);
    count.fill(0);
    misses.fill(0);
    std::vector<std::array<int,3>> coords;
    for (int x=0; x<q; ++x) for (int y=0; y<q; ++y) coords.push_back({1,x,y});
    for (int y=0; y<q; ++y) coords.push_back({0,1,y});
    coords.push_back({0,0,1});
    for (int j=0; j<n; ++j) {
        for (int i=0; i<n; ++i) {
            int dot=0;
            for (int k=0; k<3; ++k) {
                if (q == 4) dot ^= gf4(coords[i][k], coords[j][k]);
                else dot += coords[i][k]*coords[j][k];
            }
            if (dot % q) continue;
            for (Mask prev = line[j]; prev; prev &= prev-1) {
                int u = std::countr_zero(prev);
                join[i][u] = join[u][i] = j;
            }
            line[j] |= 1u << i;
            int x = 1+n*i+j, shifted = x+305;
            int square = x*x % modulus;
            weight[0][i][j] = square*square % modulus;
            weight[1][i][j] = (shifted*shifted % modulus)*shifted % modulus;
        }
    }
    for (int r=0; r<n; ++r) for (int v=r+1; v<n; ++v) {
        int j = join[r][v];
        visit(r, v, v, (1u<<r) | (1u<<v), ((1u<<(r+1))-1) | line[j],
              delta(0,r,v,j), delta(1,r,v,j));
    }
    std::cout << "PG(2," << q << ")\n";
    for (int k=0; k<=n; ++k) if (count[k]) std::cout << 2*k << " " << count[k] << "\n";
    for (int m=0; m<4; ++m) std::cout << "miss mask " << m << " " << misses[m] << "\n";
    return misses[3] == 0;
}

int main() {
    bool ok = true;
    for (auto parameters : {std::array{2,127,113}, std::array{3,511,509},
                            std::array{4,1023,1021}, std::array{5,2047,2039}}) {
        if (!check(parameters[0], parameters[1], parameters[2])) ok = false;
    }
    return ok ? 0 : 1;
}
