#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

// Each truth-table word describes one wire on the 24 promised inputs.
// The separation mask has one bit for each of the 14 accepted cells
// paired with each of the 10 rejected cells.
using Word = std::uint32_t;
constexpr Word target = 842943;
constexpr Word full = (Word{1} << 24) - 1;
constexpr unsigned max_gates = 10;
using Frontier = std::array<Word, max_gates + 1>;

struct Separation {
    std::array<std::uint64_t, 3> words{};

    void set(unsigned index) {
        words[index / 64] |= std::uint64_t{1} << (index % 64);
    }
    Separation operator|(const Separation& other) const {
        return {{words[0] | other.words[0], words[1] | other.words[1],
                 words[2] | other.words[2]}};
    }
    Separation operator&(const Separation& other) const {
        return {{words[0] & other.words[0], words[1] & other.words[1],
                 words[2] & other.words[2]}};
    }
    bool covers_all() const {
        return words[0] == UINT64_MAX && words[1] == UINT64_MAX && words[2] == 4095;
    }
};

unsigned extract(Word value, Word positions) {
    unsigned packed = 0;
    for (unsigned bit = 1; positions; bit <<= 1) {
        if (value & (positions & -positions)) packed |= bit;
        positions &= positions - 1;
    }
    return packed;
}

void sort_frontier(Frontier& frontier, unsigned size) {
    for (unsigned i = 1; i < size; ++i) {
        for (unsigned j = i; j > 0 && frontier[j] < frontier[j - 1]; --j) {
            std::swap(frontier[j], frontier[j - 1]);
        }
    }
}

struct FrontierHash {
    std::size_t operator()(const Frontier& frontier) const {
        std::size_t hash = 0;
        for (Word wire : frontier) hash = (hash * 0x9e3779b1u) ^ wire;
        return hash;
    }
};

struct Gate {
    std::string_view operation;
    Word first;
    Word second;
    Word output;
};

class Search {
    std::array<Separation, 1 << 14> positive{};
    std::array<Separation, 1 << 10> negative{};
    std::unordered_set<Frontier, FrontierHash> failed[max_gates + 1][max_gates + 1];
    std::uint64_t calls[max_gates + 1]{};
    std::vector<Gate> witness;

    Separation separates(Word wire, unsigned not_gates) const {
        auto result = positive[extract(wire, target)] & negative[extract(full ^ wire, full ^ target)];
        if (not_gates) {
            result = result | (positive[extract(full ^ wire, target)] & negative[extract(wire, full ^ target)]);
        }
        return result;
    }

    bool visit(Frontier frontier, unsigned size, unsigned gates, unsigned not_gates) {
        ++calls[gates];
        if (size == 1 && frontier[0] == target) return true;
        if (!gates || failed[gates][not_gates].contains(frontier)) return false;

        Separation cuts[max_gates + 1];
        for (unsigned i = 0; i < size; ++i) cuts[i] = separates(frontier[i], not_gates);

        // A binary gate can decrease the number of live wires by at most one.
        const unsigned keep_budget = gates + 1 - size;
        const auto end = frontier.begin() + size;
        for (unsigned i = 0; i < size; ++i) {
            for (unsigned j = 0; j < i; ++j) {
                Frontier rest{};
                unsigned rest_size = 0;
                Separation retained;
                for (unsigned k = 0; k < size; ++k) {
                    if (k == i || k == j) continue;
                    rest[rest_size++] = frontier[k];
                    retained = retained | cuts[k];
                }
                const Word first = frontier[i];
                const Word second = frontier[j];
                for (Word output : {first & second, first | second}) {
                    if (std::find(frontier.begin(), end, output) != end) continue;
                    const auto next_cuts = retained | separates(output, not_gates);
                    for (unsigned keep = 0; keep < 4; ++keep) {
                        if (static_cast<unsigned>(std::popcount(keep)) > keep_budget) continue;
                        auto coverage = next_cuts;
                        if (keep & 1) coverage = coverage | cuts[i];
                        if (keep & 2) coverage = coverage | cuts[j];
                        if (!coverage.covers_all()) continue;
                        Frontier next = rest;
                        unsigned next_size = rest_size;
                        next[next_size++] = output;
                        if (keep & 1) next[next_size++] = first;
                        if (keep & 2) next[next_size++] = second;
                        sort_frontier(next, next_size);
                        if (visit(next, next_size, gates - 1, not_gates)) {
                            witness.push_back({output == (first & second) ? "AND" : "OR", first, second, output});
                            return true;
                        }
                    }
                }
            }
        }

        if (not_gates && size <= gates) {
            for (unsigned i = 0; i < size; ++i) {
                const Word output = full ^ frontier[i];
                if (std::find(frontier.begin(), end, output) != end) continue;
                for (unsigned keep = 0; keep <= 1 && size + keep <= gates; ++keep) {
                    Frontier next{};
                    unsigned next_size = 0;
                    auto coverage = separates(output, not_gates - 1);
                    for (unsigned j = 0; j < size; ++j) {
                        if (j == i && !keep) continue;
                        next[next_size++] = frontier[j];
                        coverage = coverage | separates(frontier[j], not_gates - 1);
                    }
                    if (!coverage.covers_all()) continue;
                    next[next_size++] = output;
                    sort_frontier(next, next_size);
                    if (visit(next, next_size, gates - 1, not_gates - 1)) {
                        witness.push_back({"NOT", frontier[i], 0, output});
                        return true;
                    }
                }
            }
        }

        failed[gates][not_gates].insert(frontier);
        return false;
    }

public:
    Search() {
        for (unsigned p = 0; p < 14; ++p) {
            for (unsigned n = 0; n < 10; ++n) {
                unsigned pair = 10 * p + n;
                for (unsigned bits = 0; bits < positive.size(); ++bits) {
                    if ((bits >> p) & 1) positive[bits].set(pair);
                }
                for (unsigned bits = 0; bits < negative.size(); ++bits) {
                    if ((bits >> n) & 1) negative[bits].set(pair);
                }
            }
        }
    }

    void run(unsigned gates, unsigned not_gates) {
        std::array<Word, 10> inputs{};
        for (unsigned row = 0; row < 4; ++row) inputs[row] = 63u << (6 * row);
        for (unsigned column = 0; column < 6; ++column) {
            for (unsigned row = 0; row < 4; ++row) inputs[4 + column] |= Word{1} << (6 * row + column);
        }

        unsigned initial_frontiers = 0;
        unsigned min_inputs = inputs.size();
        for (unsigned mask = 1; mask < 1u << inputs.size(); ++mask) {
            Frontier frontier{};
            unsigned size = 0;
            Separation coverage;
            for (unsigned i = 0; i < inputs.size(); ++i) {
                if (!((mask >> i) & 1)) continue;
                frontier[size++] = inputs[i];
                coverage = coverage | separates(inputs[i], not_gates);
            }
            if (!coverage.covers_all()) continue;
            min_inputs = std::min(min_inputs, size);
            if (size > gates + 1) continue;
            ++initial_frontiers;
            sort_frontier(frontier, size);
            if (!visit(frontier, size, gates, not_gates)) continue;
            for (auto gate = witness.rbegin(); gate != witness.rend(); ++gate) {
                std::cout << gate->operation << ' ' << gate->first;
                if (gate->operation != "NOT") std::cout << ' ' << gate->second;
                std::cout << " -> " << gate->output << '\n';
            }
            std::cout << "SAT\n";
            return;
        }

        std::uint64_t total_calls = 0;
        std::size_t total_failed = 0;
        for (unsigned remaining = 0; remaining <= gates; ++remaining) {
            total_calls += calls[remaining];
            for (unsigned negations = 0; negations <= not_gates; ++negations) {
                total_failed += failed[remaining][negations].size();
            }
        }
        std::cout << "UNSAT; initial frontiers: " << initial_frontiers
                  << "; minimum inputs: " << min_inputs << "; visits: " << total_calls
                  << "; memoized failures: " << total_failed << '\n';
    }
};

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr << "Usage: replay GATES NOT_GATES\n";
        return 2;
    }
    const int gates = std::stoi(argv[1]);
    const int not_gates = std::stoi(argv[2]);
    if (gates < 0 || gates > static_cast<int>(max_gates) || not_gates < 0 || not_gates > gates) {
        std::cerr << "Require 0 <= NOT_GATES <= GATES <= 10\n";
        return 2;
    }
    Search search;
    search.run(gates, not_gates);
}
