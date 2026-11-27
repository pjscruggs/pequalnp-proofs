# Two evaluations for projective-plane minors

A fixed pair of assignments detects every nonzero determinant with at most two matching terms in the incidence pattern of PG(2,q) at orders 2, 3, 4 and 5. The same rule misses an explicit two-term determinant at order 7. The evaluation field has the size prescribed in [discussion #37019](https://github.com/open-goat/pequalnp-proofs/discussions/37019).

## Certificate

Put $N=q^2+q+1$. Let $Q$ be the smallest power of two greater than $2N^2+1$, and let $p$ be the largest prime strictly below $Q-1$. Use the normalized coordinate triples $(1,x,y)$ in lexicographic order, then $(0,1,y)$, then $(0,0,1)$, for both rows and columns. Index from zero. For GF(4), encode $0,1,t,t+1$ as 0,1,2,3 with $t^2=t+1$. Incidence means zero dot product in the plane's field.

With $g$ any generator of the multiplicative group of GF($Q$), put $x=1+Ni+j$ at incidence $(i,j)$. The two assignments give it the values $g^{x^4\bmod p}$ and $g^{(x+305)^3\bmod p}$, using least nonnegative residues. Off-incidence entries are zero. The shift was selected by finite search at order five.

| Plane order | Evaluation field size | Induced cycles | Missed by first | Missed by second | Missed by both |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 128 | 49 | 0 | 0 | 0 |
| 3 | 512 | 1,404 | 3 | 2 | 0 |
| 4 | 1,024 | 101,416 | 93 | 90 | 0 |
| 5 | 2,048 | 28,192,175 | 13,758 | 13,750 | 0 |

A unique matching gives a nonzero product under either assignment. If a minor has exactly two matchings, their symmetric difference is one alternating cycle, since disjoint cycles could be flipped separately. A chord on the cycle would itself complete to a third matching. Common edges of the original matchings have nonzero values. Thus checking inequality of the two alternating exponent sums modulo $Q-1$ on every induced cycle suffices. The counts give a two-query upper bound at orders four and five. The minimum at those orders remains open.

## Replay

Run from the directory containing these files with a C++20 compiler and Python 3.

```sh
c++ -std=c++20 -O3 plane_certificate.cpp -o plane_certificate
./plane_certificate
python3 order_seven_obstruction.py
```

The C++ checker grows paths of points. Each new secant must avoid all earlier points except its predecessor, and the new point must avoid every earlier secant. The closing secant must meet the point set only at the endpoints. Starting at the least point and choosing one orientation counts each cycle once. Its four output masks indicate neither assignment failed, only the first failed, only the second failed, or both failed. The last count is zero at each of the four orders. A separate alternating point–line traversal agreed on every cycle length and failure count at orders four and five. An additional order-four check used field multiplication in GF(1024).

At order seven the Python checker verifies the induced incidences of a 14-by-14 minor. The two matching exponents are both 6,510 under the first assignment and both 530 under the second, modulo 8,191. This rules out extrapolating these particular formulas to every order.
