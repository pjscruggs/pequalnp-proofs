// Complete finite live-wire search for small monotone one-a-side tables.
// Derived from the checked live-wire method used in L-meta-6343 and L-meta-20636.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <utility>
#include <vector>

using Word = uint32_t;
using Cut = std::bitset<256>;
using State = std::array<Word, 12>;

struct Hash {
    size_t operator()(const State& state) const {
        size_t value = 0;
        for (Word wire : state) value = value * 0x9e3779b1 + wire;
        return value;
    }
};

struct Gate { bool use_or; Word a, b, out; };

struct Search {
    Word goal, full;
    uint64_t limit, visited = 0;
    bool cutoff = false;
    Cut all;
    std::vector<unsigned> positive, negative;
    std::vector<Cut> positive_parts, negative_parts;
    std::vector<Gate> trail;
    std::vector<std::unordered_set<State, Hash>> failed;

    Search(Word target, unsigned cells, unsigned max_gates, uint64_t node_limit)
        : goal(target), full((Word(1) << cells) - 1), limit(node_limit), failed(max_gates + 1) {
        for (unsigned bit = 0; bit < cells; ++bit)
            ((goal >> bit & 1) ? positive : negative).push_back(bit);
        positive_parts.resize(size_t(1) << positive.size());
        negative_parts.resize(size_t(1) << negative.size());
        std::vector<Cut> p(positive.size()), n(negative.size());
        for (unsigned i = 0; i < positive.size(); ++i)
            for (unsigned j = 0; j < negative.size(); ++j) {
                unsigned index = i * negative.size() + j;
                p[i].set(index);
                n[j].set(index);
                all.set(index);
            }
        for (unsigned i = 1; i < positive_parts.size(); ++i)
            positive_parts[i] = positive_parts[i & (i - 1)] | p[std::countr_zero(i)];
        for (unsigned i = 1; i < negative_parts.size(); ++i)
            negative_parts[i] = negative_parts[i & (i - 1)] | n[std::countr_zero(i)];
    }

    Cut separates(Word wire) const {
        unsigned p = 0, n = 0;
        for (unsigned i = 0; i < positive.size(); ++i) p |= (wire >> positive[i] & 1) << i;
        for (unsigned i = 0; i < negative.size(); ++i) n |= (1 ^ (wire >> negative[i] & 1)) << i;
        return positive_parts[p] & negative_parts[n];
    }

    bool visit(const State& live, unsigned count, unsigned room) {
        if (++visited > limit) { cutoff = true; return false; }
        if (count == 1 && live[0] == goal) return true;
        if (room == 0 || count < 2 || failed[room].contains(live)) return false;
        std::array<Cut, 12> cuts;
        for (unsigned i = 0; i < count; ++i) cuts[i] = separates(live[i]);
        for (unsigned i = 0; i < count; ++i) {
            for (unsigned j = i + 1; j < count; ++j) {
                State remaining{};
                unsigned base_count = 0;
                Cut covered;
                for (unsigned k = 0; k < count; ++k) if (k != i && k != j) {
                    remaining[base_count++] = live[k];
                    covered |= cuts[k];
                }
                for (bool disjunction : {false, true}) {
                    const Word z = disjunction ? live[i] | live[j] : live[i] & live[j];
                    if (z == 0 || z == full || std::binary_search(live.begin(), live.begin() + count, z)) continue;
                    const Cut with_result = covered | separates(z);
                    for (unsigned keep = 0; keep < 4; ++keep) {
                        if (base_count + 1 + std::popcount(keep) > room) continue;
                        Cut required = with_result;
                        if (keep & 1) required |= cuts[i];
                        if (keep & 2) required |= cuts[j];
                        if (required != all) continue;
                        State next = remaining;
                        unsigned size = base_count;
                        next[size++] = z;
                        if (keep & 1) next[size++] = live[i];
                        if (keep & 2) next[size++] = live[j];
                        std::sort(next.begin(), next.begin() + size);
                        trail.push_back({disjunction, live[i], live[j], z});
                        if (visit(next, size, room - 1)) return true;
                        trail.pop_back();
                        if (cutoff) return false;
                    }
                }
            }
        }
        failed[room].insert(live);
        return false;
    }

    bool run(const std::vector<Word>& inputs, unsigned budget) {
        std::vector<Cut> cuts;
        for (auto wire : inputs) cuts.push_back(separates(wire));
        for (unsigned subset = 1; subset < (1u << inputs.size()); ++subset) {
            if (unsigned(std::popcount(subset)) > budget + 1) continue;
            State live{};
            Cut coverage;
            unsigned count = 0;
            for (unsigned i = 0; i < inputs.size(); ++i) if (subset >> i & 1) {
                live[count++] = inputs[i];
                coverage |= cuts[i];
            }
            if (coverage != all) continue;
            std::sort(live.begin(), live.begin() + count);
            if (visit(live, count, budget)) return true;
            if (cutoff) return false;
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 6) return 2;
    const unsigned rows = std::stoul(argv[1]), columns = std::stoul(argv[2]), budget = std::stoul(argv[4]);
    const Word target = std::stoul(argv[3]);
    const unsigned cells = rows * columns;
    if (rows < 2 || columns < 2 || cells > 24 || rows + columns > 11 || budget > 11 || target >= (1u << cells)) return 2;
    const Word full = (1u << cells) - 1;
    if (target == 0 || target == full) {
        std::cout << ((target == 0 || budget > 0) ? "SAT" : "UNSAT") << " 0\n";
        if (target == full && budget > 0) std::cout << "and\n";
        if (target == 0) std::cout << "output " << rows + columns << '\n';
        else if (budget > 0) std::cout << "output " << rows + columns << '\n';
        return 0;
    }
    std::vector<Word> inputs(rows + columns);
    for (unsigned i = 0; i < rows; ++i)
        for (unsigned j = 0; j < columns; ++j) {
            const Word bit = 1u << (i * columns + j);
            inputs[i] |= bit;
            inputs[rows + j] |= bit;
        }
    Search search(target, cells, budget, std::stoull(argv[5]));
    const bool found = search.run(inputs, budget);
    std::cout << (found ? "SAT" : search.cutoff ? "LIMIT" : "UNSAT") << ' ' << search.visited << '\n';
    if (found) {
        for (const auto& gate : search.trail) {
            const auto a = std::find(inputs.begin(), inputs.end(), gate.a) - inputs.begin();
            const auto b = std::find(inputs.begin(), inputs.end(), gate.b) - inputs.begin();
            std::cout << (gate.use_or ? "or" : "and") << ' ' << a << ' ' << b << '\n';
            inputs.push_back(gate.out);
        }
        std::cout << "output " << std::find(inputs.begin(), inputs.end(), target) - inputs.begin() << '\n';
    }
}
