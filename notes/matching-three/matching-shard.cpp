#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>


using namespace std;
using Word=uint32_t;
using Frontier=array<Word,14>;
struct Hash {
    size_t operator()(const Frontier& words) const {
        size_t hash=0;
        for (Word word:words) hash=(0x9e3779b1u*hash)^word;
        return hash;
    }
};
struct Bits {
    uint64_t low=0,high=0;
    Bits operator|(Bits other) const { return {low|other.low,high|other.high}; }
    bool operator==(const Bits&) const = default;
};
struct Separation {
    Bits directed,both;
    Separation operator|(Separation other) const {
        return {directed|other.directed,both|other.both};
    }
};
struct Gate {int op;Word a,b,out;};

constexpr unsigned max_word=1<<21;
Separation cache[max_word];
unsigned epochs[max_word];
unsigned epoch=0;
Word target,full,points;
Bits complete;
unsigned negatives;
uint64_t calls;
uint64_t visit_limit=5'000'000;
vector<Gate> witness;
unordered_set<Frontier,Hash> failed[14][14];

Bits broadcast(unsigned positives,unsigned rejected) {
    Bits out;
    const uint64_t block=rejected;
    while (positives) {
        const unsigned offset=negatives*countr_zero(positives);
        positives&=positives-1;
        if (offset>=64) {
            out.high|=block<<(offset-64);
        } else {
            out.low|=block<<offset;
            if (offset && offset+negatives>64) out.high|=block>>(64-offset);
        }
    }
    return out;
}
Word extract_bits(Word word, Word positions) {
    Word packed = 0;
    for (Word bit = 1; positions; bit <<= 1) {
        if (word & (positions & -positions)) packed |= bit;
        positions &= positions - 1;
    }
    return packed;
}

Separation cuts(Word word) {
    if (epochs[word]==epoch) return cache[word];
    const auto p=extract_bits(word,target), n=extract_bits(word,full^target);
    const auto p_other=(1u<<popcount(target))-1-p;
    const auto n_other=(1u<<negatives)-1-n;
    const auto fwd=broadcast(p,n_other);
    const auto back=broadcast(p_other,n);
    epochs[word]=epoch;
    return cache[word]={fwd,fwd|back};
}
bool separates(Separation s,unsigned nots) {
    return (nots?s.both:s.directed)==complete;
}
void sort_frontier(Frontier& frontier,unsigned size) {
    for (unsigned i=1;i<size;++i)
        for (unsigned j=i;j && frontier[j]<frontier[j-1];--j) swap(frontier[j],frontier[j-1]);
}
bool visit(Frontier frontier,unsigned size,unsigned gates,unsigned nots) {
    if (++calls>visit_limit) throw 1;
    if (size==1 && frontier[0]==target) return true;
    if (!gates || failed[gates][nots].contains(frontier)) return false;
    Separation word_cuts[14];
    for (unsigned i=0;i<size;++i) word_cuts[i]=cuts(frontier[i]);
    const unsigned slack=gates+1-size;
    const auto end=frontier.begin()+size;
    for (unsigned i=0;i<size;++i) for (unsigned j=0;j<i;++j) {
        Frontier rest{};
        unsigned retained_size=0;
        Separation retained;
        for (unsigned k=0;k<size;++k) if (k!=i && k!=j) {
            retained=retained|word_cuts[k];
            rest[retained_size++]=frontier[k];
        }
        const auto a=frontier[i],b=frontier[j];
        for (Word out:{a&b,a|b}) {
            if (!out || out==full || find(frontier.begin(),end,out)!=end) continue;
            const auto coverage=retained|cuts(out);
            for (unsigned keep=0;keep<4;++keep) {
                const auto count=unsigned(popcount(keep));
                if (count>slack) continue;
                const unsigned next_nots=min(nots,slack-count);
                auto s=coverage;
                if (keep&1) s=s|word_cuts[i];
                if (keep&2) s=s|word_cuts[j];
                if (!separates(s,next_nots)) continue;
                Frontier next=rest;
                unsigned next_size=retained_size;
                next[next_size++]=out;
                if (keep&1) next[next_size++]=a;
                if (keep&2) next[next_size++]=b;
                sort_frontier(next,next_size);
                if (visit(next,next_size,gates-1,next_nots)) {
                    witness.push_back({out==(a&b)?0:1,a,b,out});
                    return true;
                }
            }
        }
    }
    if (nots && size<=gates) for (unsigned i=0;i<size;++i) {
        const Word a=frontier[i],out=full^a;
        if (find(frontier.begin(),end,out)!=end) continue;
        for (unsigned keep=0;keep<=1 && size+keep<=gates;++keep) {
            Frontier next{};
            unsigned next_size=0;
            auto coverage=cuts(out);
            for (unsigned k=0;k<size;++k) if (k!=i || keep) {
                next[next_size++]=frontier[k];
                coverage=coverage|word_cuts[k];
            }
            const unsigned next_nots=min(nots-1,gates-size-keep);
            if (!separates(coverage,next_nots)) continue;
            next[next_size++]=out;
            sort_frontier(next,next_size);
            if (visit(next,next_size,gates-1,next_nots)) {
                witness.push_back({2,a,a,out});
                return true;
            }
        }
    }
    failed[gates][nots].insert(frontier);
    return false;
}


int main(int argc, char** argv) {
    if (argc != 4) return 4;
    const unsigned cap = stoul(argv[1]), not_limit = stoul(argv[2]);
    if (cap < 8 || cap > 13 || not_limit > cap-8) return 4;
    visit_limit = stoull(argv[3]);
    epoch = 1;
    points = 9;
    full = (1u<<21)-1;
    target = 63;
    negatives = 15;
    complete = broadcast(63, (1u<<15)-1);
    Frontier initial{220099,368332,652016,1207764,1355617,1635658,2050472,2067986,2093061};
    sort_frontier(initial,9);
    try {
        if (visit(initial,9,cap,not_limit)) {
            cout << "PRESENT " << calls << endl;
            return 1;
        }
        cout << "EXHAUSTED " << calls << endl;
        return 0;
    } catch (int) {
        cout << "CAPPED " << calls << endl;
        return 3;
    }
}
