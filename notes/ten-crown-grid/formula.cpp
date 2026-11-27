#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using U = std::uint64_t;
constexpr U P0 = ((U{1} << 45) - 1) << 10, N0 = 1023, ALL = P0 | N0;
struct Term {
  U w;
  int cost, op, a, b;
};
struct Obl {
  U p, n;
  int k;
  bool operator==(const Obl &) const = default;
};
struct Hash {
  std::size_t operator()(const Obl &x) const {
    return (x.p * 0x9e3779b97f4a7c15ULL) ^ (x.n * 0xbf58476d1ce4e5b9ULL) ^ x.k;
  }
};
struct Option {
  U p, n;
  int z, op, score;
};
std::vector<Term> terms;
std::vector<std::vector<int>> layers;
std::unordered_map<U, int> idx;
std::unordered_set<Obl, Hash> memo;
int cap, maxSmall, maxCalls, calls;
std::vector<std::array<U, 10>> forced;
bool useRect = true;
int leafBound(U p, U n, int room) {
  std::array<U, 28> rows{}, cols{};
  unsigned present = 0;
  for (unsigned a = 0; a < forced.size(); a++) {
    for (unsigned neg = n; neg; neg &= neg - 1) {
      int j = std::countr_zero(neg);
      U s = forced[a][j] & p;
      if (s) {
        rows[a] |= s;
        cols[a] |= U{1} << j;
      }
    }
    if (rows[a])
      present |= 1u << a;
  }
  int used = std::popcount(present);
  if (used > room || 2 * used <= room)
    return used;
  std::array<unsigned, 28> adj{};
  unsigned edgeEnds = 0;
  for (unsigned u = present; u; u &= u - 1) {
    int a = std::countr_zero(u);
    for (unsigned v = u & (u - 1); v; v &= v - 1) {
      int b = std::countr_zero(v);
      if ((rows[a] & rows[b]) && (cols[a] & cols[b])) {
        adj[a] |= 1u << b;
        adj[b] |= 1u << a;
        edgeEnds |= (1u << a) | (1u << b);
      }
    }
  }
  auto cover = [&](auto &&self, unsigned left, int lim) -> bool {
    if (lim < 0)
      return false;
    int best = -1, deg = 0;
    for (unsigned v = left; v; v &= v - 1) {
      int a = std::countr_zero(v), d = std::popcount(adj[a] & left);
      if (d > deg) {
        best = a;
        deg = d;
      }
    }
    if (best < 0)
      return true;
    return self(self, left & ~(1u << best), lim - 1) ||
           (deg <= lim && self(self, left & ~adj[best], lim - deg));
  };
  return cover(cover, edgeEnds, room - used) ? used : room + 1;
}
int put(U w, int cost, int op, int a, int b) {
  int z = terms.size();
  terms.push_back({w, cost, op, a, b});
  return z;
}
void prepare(const std::vector<U> &inputs) {
  terms.clear();
  idx.clear();
  layers.assign(maxSmall + 1, {});
  forced.assign(inputs.size(), {});
  for (int i = 10; i < 55; i++)
    for (int j = 0; j < 10; j++) {
      int f = -1;
      for (int a = 0; a < (int)inputs.size(); a++)
        if ((inputs[a] >> i & 1) && !(inputs[a] >> j & 1)) {
          if (f >= 0) {
            f = -1;
            break;
          }
          f = a;
        }
      if (f >= 0)
        forced[f][j] |= U{1} << i;
    }
  for (U w : inputs) {
    int z = put(w, 0, -1, 0, 0);
    layers[0].push_back(z);
    idx[w] = z;
  }
  for (int k = 1; k <= maxSmall; k++)
    for (int i = 0; i <= (k - 1) / 2; i++)
      for (int x : layers[i])
        for (int y : layers[k - 1 - i]) {
          if (i == k - 1 - i && x >= y)
            continue;
          for (int op = 0; op < 2; op++) {
            U w = op ? terms[x].w | terms[y].w : terms[x].w & terms[y].w;
            if (w == 0 || w == ALL || idx.contains(w))
              continue;
            int z = put(w, k, op, x, y);
            idx[w] = z;
            layers[k].push_back(z);
          }
        }
}
int solve(U p, U n, int k) {
  if (calls >= maxCalls)
    return -1;
  if (!memo.insert({p, n, k}).second)
    return -1;
  calls++;
  int direct = std::min(k, maxSmall);
  if (useRect && leafBound(p, n, k + 1) > k + 1)
    return -1;
  for (int t = 0; t <= direct; t++)
    for (int z : layers[t])
      if (!(terms[z].w & n) && !(p & ~terms[z].w))
        return z;
  if (k <= maxSmall)
    return -1;
  std::vector<Option> todo;
  for (int t = 0; t <= std::min(maxSmall, (k - 1) / 2); t++)
    for (int z : layers[t]) {
      U w = terms[z].w;
      if (!(w & n) && (p & w)) {
        U rem = p & ~w;
        int score = 100 * std::popcount(w & p) / (t + 1);
        todo.push_back({rem, n, z, 1, score});
      }
      if (!(p & ~w) && (n & ~w)) {
        U rem = n & w;
        int score = 300 * std::popcount(n & ~w) / (t + 1);
        todo.push_back({p, rem, z, 0, score});
      }
    }
  std::stable_sort(
      todo.begin(), todo.end(),
      [](const Option &a, const Option &b) { return a.score > b.score; });
  for (const auto &o : todo) {
    int y = solve(o.p, o.n, k - 1 - terms[o.z].cost);
    if (y >= 0) {
      U w = o.op ? terms[o.z].w | terms[y].w : terms[o.z].w & terms[y].w;
      return put(w, 1 + terms[o.z].cost + terms[y].cost, o.op, o.z, y);
    }
    if (calls >= maxCalls)
      break;
  }
  return -1;
}
int emit(int t, int m, std::vector<std::array<int, 3>> &gs,
         std::unordered_map<int, int> &wires) {
  if (t < m)
    return t;
  if (wires.contains(t))
    return wires[t];
  auto g = terms[t];
  int a = emit(g.a, m, gs, wires), b = emit(g.b, m, gs, wires);
  int i = m + gs.size();
  gs.push_back({g.op, a, b});
  return wires[t] = i;
}
#ifndef GRID_FORMULA_LIBRARY
int main(int argc, char **argv) {
  if (argc < 5)
    return 2;
  std::ifstream file(argv[1]);
  maxCalls = std::stoi(argv[2]);
  int ceiling = std::stoi(argv[3]), bonus = std::stoi(argv[4]);
  std::string name;
  int m, k;
  while (file >> name >> m >> k) {
    k += bonus;
    std::vector<U> inputs;
    if (name.starts_with("W_")) {
      for (int u = 0; u < m; u++) {
        U w;
        file >> w;
        inputs.push_back(w);
      }
    } else {
      std::array<int, 10> cc{};
      for (auto &z : cc)
        file >> z;
      for (int u = 0; u < m; u++) {
        U w = 0;
        int bit = 10;
        for (int i = 0; i < 10; i++)
          if (cc[i] & (1 << u))
            w |= U{1} << i;
        for (int i = 0; i < 10; i++)
          for (int j = i + 1; j < 10; j++, bit++)
            if ((cc[i] | cc[j]) & (1 << u))
              w |= U{1} << bit;
        inputs.push_back(w);
      }
    }
    maxSmall = std::min(ceiling, (k - 1) / 2);
    prepare(inputs);
    int labels = terms.size();
    memo.clear();
    calls = 0;
    int w = solve(P0, N0, k);
    std::cout << name << " " << k << " " << calls << " " << labels << " "
              << (w >= 0                   ? "found"
                  : calls >= maxCalls      ? "limit"
                  : maxSmall < (k - 1) / 2 ? "restricted"
                                           : "exhausted");
    if (w >= 0) {
      std::vector<std::array<int, 3>> gs;
      std::unordered_map<int, int> wires;
      emit(w, m, gs, wires);
      for (auto g : gs)
        std::cout << " " << g[0] << "," << g[1] << "," << g[2];
    }
    std::cout << std::endl;
  }
}
#endif
