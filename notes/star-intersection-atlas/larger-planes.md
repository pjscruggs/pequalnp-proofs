# Lower bounds that grow with the order of the plane

Let a circuit construct a graph from its row and column stars, using arbitrary unions, wire reuse, and $k$ binary intersections. Let $Z$ be the zero-one matrix of the cells outside the output graph. Two bounds on $k$ complement the four-intersection quadrangle certificate.

## Rank of the zero-cell matrix

**Claim.** Over the reals, $\operatorname{rank}(Z)\le 3^k$. The bound is attained for each $k$.

To prove the inequality, work with indicators of zero cells. The zero set of any union of original stars is a rectangle. Once $j$ paid gates have been evaluated, the zero indicator of a free union of available wires is an entrywise product of a rectangle indicator and a subset of the $j$ paid zero indicators. The entire grid represents an empty product. If a paid intersection has operands with zero indicators $P,Q$, its own zero indicator is $P+Q-PQ$, with entrywise multiplication.

Start with the free union at the output and eliminate the paid variables in reverse topological order. Within each monomial, repeated indicators are idempotent. Substituting for one variable therefore gives at most three monomials per existing monomial, even if its wire was reused many times. After $k$ eliminations there are at most $3^k$ signed terms. Each term is a product of rectangle indicators, hence the indicator of a rectangle and of rank at most one. Rank subadditivity gives the claim.

For sharpness, let $B$ be the three-by-three matrix with rows $(1,0,1),(0,1,1),(1,1,1)$. It is the union of $\{1,3\}\times\{1,3\}$ and $\{2,3\}\times\{2,3\}$ and has determinant $-1$. On words of length $k$ over three symbols, intersect the $k$ coordinatewise copies of that union. Every coordinate rectangle's complement is a free union of original stars. Thus in the zero-set representation each coordinate needs one paid union, and combining the coordinates needs only free intersections. The resulting matrix is $B^{\otimes k}$ and has rank $3^k$.

## Projective planes

For a finite projective plane of order $q$, put $N=q^2+q+1$. The zero matrix of its incidence graph is the nonincidence matrix $Z$. A row has $q^2$ ones. Two different rows share $q^2-q$ ones, because two points lie together on exactly one line. Hence $ZZ^\top=qI+(q^2-q)J$, with $J$ the all-ones matrix. This matrix is positive definite. The rank bound gives $N\le3^k$.

An independent counting argument gives $N\le\binom{2k}{k}$. Normalize the circuit by writing each operand of each paid gate as a free union of raw stars and earlier paid outputs. Record for each row the $2k$ bits saying which of those operands select its raw star. No raw row star can appear in the final free union because the incidence graph has no full row. For a fixed column, all other raw row stars evaluate to zero and the column-star contributions are fixed. The output is consequently monotone in those $2k$ bits. Inclusion of two row signatures would imply inclusion of the corresponding neighborhoods. In a plane the neighborhoods are distinct and have the same size $q+1$, so the signatures form an antichain. Sperner's theorem gives the inequality.

| Plane order | Number of points | Certified lower bound on intersections | Reason |
|---:|---:|---:|---|
| 2 | 7 | 4 | Quadrangle restriction |
| 8 | 73 | 5 | $\binom{8}{4}=70<73$ |
| 16 | 273 | 6 | $3^5=243<273$ |
| 27 | 757 | 7 | $3^6=729<757$ |

These estimates apply to star circuits on the point–line domain and give logarithmic growth in the number of points. They leave a superlogarithmic lower bound open. Cavalar and Oliveira also give an exact logarithmic bound for the crown graph in this circuit model. [Cavalar and Oliveira, §4.2, Proposition 40](https://arxiv.org/html/2503.14117v1#S4.SS2)
