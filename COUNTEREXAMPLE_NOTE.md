# Human proof note

Let `H` be the bipartite graph obtained from `K_{5,5}` with left part `{0,1,2,3,4}` and right part `{5,6,7,8,9}` by deleting `(0,5)`, `(0,6)`, `(0,7)`, and `(1,5)`.

Add seven isolated vertices `10,...,16`, then add a universal vertex `17`; call the resulting connected graph `G`.

## Bipartite order

Deleting vertex `17` leaves a bipartite graph on 17 vertices, so `b(G) ≥ 17`.

## Induced forest order

Any selected set of at least 14 vertices has a cycle:

- If it contains `17`, the remaining selected non-center vertices contain an edge, which forms a triangle with `17`.
- If it omits `17`, it contains at least 14 of the 17 non-center vertices; an exhaustive finite certificate finds a 4-cycle in the ten-vertex core.

Thus `f(G) ≤ 13`.

## Residue

The exact Havel–Hakimi computation on the degree sequence leaves ten zeros, so `residue(G)=10`.

Therefore

`residue(G) * b(G) ≥ 10 * 17 = 170 > 169 = 13^2`, 

and consequently

`ceil(sqrt(residue(G) * b(G))) ≥ 14 > 13 ≥ f(G)`.

So Written on the Wall II Conjecture 59 is false.
