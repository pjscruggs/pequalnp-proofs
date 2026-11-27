#define GRID_FORMULA_LIBRARY
#include "formula.cpp"
struct Ends {
  U lo, hi;
  bool operator==(const Ends &) const = default;
};
struct EndHash {
  std::size_t operator()(const Ends &v) const {
    return v.lo * 0x9e3779b97f4a7c15ULL ^ v.hi * 0xbf58476d1ce4e5b9ULL;
  }
};
struct ParTerm {
  Ends v;
  int op, a, b;
};
int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  std::ifstream f(argv[1]);
  std::string nm;
  int m, k;
  std::array<int, 10> cc;
  f >> nm >> m >> k;
  for (int &c : cc)
    f >> c;
  std::vector<U> raw;
  std::vector<ParTerm> par;
  std::vector<std::vector<int>> level(6);
  std::unordered_set<Ends, EndHash> seen;
  auto admit = [&](int cost, Ends v, int op, int l, int r) {
    if (!seen.insert(v).second)
      return;
    level[cost].push_back(par.size());
    par.push_back({v, op, l, r});
  };
  for (int u = 0; u < m; u++) {
    U w = 0;
    int bit = 10;
    for (int i = 0; i < 10; i++)
      if (cc[i] >> u & 1)
        w |= U{1} << i;
    for (int i = 0; i < 10; i++)
      for (int j = i + 1; j < 10; j++, bit++)
        if ((cc[i] | cc[j]) >> u & 1)
          w |= U{1} << bit;
    raw.push_back(w);
    admit(0, {w, w}, -1, u, 0);
  }
  admit(0, {0, ALL}, -1, m, 0);
  for (int g = 1; g <= 5; g++)
    for (int i = 0; i <= (g - 1) / 2; i++)
      for (int x : level[i])
        for (int y : level[g - 1 - i]) {
          if (i == g - 1 - i && x >= y)
            continue;
          auto a = par[x].v, b = par[y].v;
          admit(g, {a.lo & b.lo, a.hi & b.hi}, 0, x, y);
          admit(g, {a.lo | b.lo, a.hi | b.hi}, 1, x, y);
        }
  maxSmall = 5;
  maxCalls = 3000000;
  prepare(raw);
  for (int u = 0; u <= 5; u++) {
    int feasible = 0, found = 0, unknown = 0, maximum = 0;
    for (int j : level[u]) {
      auto [lo, hi] = par[j].v;
      if ((lo & N0) || (P0 & ~hi))
        continue;
      feasible++;
      memo.clear();
      calls = 0;
      int z = solve(P0 & ~lo, N0 & hi, k - u);
      maximum = std::max(maximum, calls);
      if (z >= 0) {
        ++found;
        std::vector<std::array<int, 3>> gs;
        std::unordered_map<int, int> ws;
        int p = emit(z, m, gs, ws);
        std::unordered_map<int, int> ss;
        auto suffix = [&](auto &&self, int t) -> int {
          auto g = par[t];
          if (g.op < 0)
            return g.a == m ? p : g.a;
          if (ss.contains(t))
            return ss[t];
          int a = self(self, g.a), b = self(self, g.b);
          int v = m + gs.size();
          gs.push_back({g.op, a, b});
          return ss[t] = v;
        };
        suffix(suffix, j);
        std::cout << nm << " " << k << " " << calls << " " << par.size()
                  << " found";
        for (auto g : gs)
          std::cout << " " << g[0] << "," << g[1] << "," << g[2];
        std::cout << std::endl;
      } else if (calls >= maxCalls)
        ++unknown;
    }
    std::cout << "suffix " << u << " words " << level[u].size()
              << " compatible " << feasible << " solved " << found
              << " cutoffs " << unknown << " max " << maximum << std::endl;
  }
}
