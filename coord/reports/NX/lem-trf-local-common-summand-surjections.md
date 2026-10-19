# Stage 1 report: lem-trf-local-common-summand-surjections

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-local-common-summand-surjections.json`: split item; eight proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-vector-subspace-complement.json`: Mathlib leaf, `Submodule.exists_isCompl`.
- `dag/nodes/sec-trace-formula/lem-trf-equal-dimension-linear-equivalence.json`: Mathlib leaf, `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`.
- `citations.json`: verbatim statement quotes for every cited proof step.

## Attachments

None. I searched the slopmaster2 source for the item id and its mathematical names; no sorry-free declaration states this item.

## WANTED

None. The cited source and the Mathlib declarations are available locally.

## What was wrong or incomplete in the imported material

Stacks Tag 0FJK states the common-summand construction but says only “some details omitted.” The imported item had no proof steps. I supplied the omitted residue-field construction and the lift to the local ring. I did not change the item statement or its hypotheses.

The source's sentence “If $R$ is a field, this is possible by linear algebra” is made precise by the two Mathlib leaves: existence of a complement to every subspace and existence of a linear equivalence between finite-dimensional spaces of equal dimension. The local-ring lift uses the existing node `lem-sc-local-free-base-change-reflects-iso`, whose statement exactly reflects an isomorphism of finite free modules along a local ring map.

## Not duplicates

- `lem-trf-vector-subspace-complement` vs `lem-sc-local-free-base-change-reflects-iso`: the former is the field-linear-algebra existence of a complement to one subspace; the latter reflects finite-free isomorphisms along a local ring map and says nothing about complements.
- `lem-trf-equal-dimension-linear-equivalence` vs `lem-weil-pbc-idempotent-charpoly-rank-nullity`: the former constructs an isomorphism from equality of dimensions; the latter states rank-nullity for one linear map.

## Review by NX

I read `literature/stacks-project/more-algebra.tex`, Tag 0FJK, including the final paragraph of the proof of `lemma-homotopic-surjections` at the exact place recorded in the item. I also read the current item JSON, the inherited blueprint ancestry, and the source declarations searched in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; no finished declaration or attachment was present. The statement remains exactly the Stacks auxiliary assertion: a commutative local ring, two surjections $R^n\to R^m$, and one common summand on which both maps are isomorphisms, including $m,n=0$.

Step 1 checks the quotient by the unique maximal ideal is a field, that reduction is a local homomorphism, and that the two reduced maps remain surjective. The only cited definition is the stated free-module notion. Step 2 applies the new complement leaf to $A\cap B$, $A$, $B$, and $A+B$, and explains why all resulting subspaces are finite-dimensional. Step 3 applies the existing rank-nullity leaf to the two reduced surjections and to the projection maps, then applies the equal-dimension linear-equivalence leaf. The hypotheses of each cited statement are present: the reduced source is finite-dimensional, and the kernels and projections are linear maps. Step 4 writes the direct coordinate decomposition and defines the graph plus the complement $D$ explicitly. Step 5 verifies both sums and both intersections by coordinates, then derives bijectivity of the restrictions. Steps 4 and 5 are elementary calculations from the decompositions and definitions, so they cite no hidden theorem.

Step 6 reads the existing base-change definition and checks the explicit identifications $R^t\otimes_R k\cong k^t$ on standard generators and pure tensors; the reduced maps are exactly $aq$ and $bq$. Step 7 uses `lem-sc-local-free-base-change-reflects-iso` exactly as stated: the map $R\to k$ is local and both maps are between finite free modules, with isomorphic scalar extensions. Step 8 identifies the image of the injective lift with the desired submodule and proves the two direct-sum decompositions by the standard decomposition $x=(x-u)+u$.

I read each new Mathlib declaration at the recorded source lines. `Submodule.exists_isCompl` supplies precisely a complementary subspace, and `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq` supplies precisely a linear equivalence under equal finite rank; neither is a duplicate of the existing rank-nullity or local-base-change nodes. I tested the construction in the edge cases $m=0$, $n=0$, $m=n=0$, and $A=B$ (then the graph part is zero and $D$ supplies the complement); the coordinate proof still works. The empty standard bases are explicitly allowed. Every non-elementary citation is included in `citations.json` with a verbatim quote from the cited node statement.

The item’s blueprint ancestry is `lem-trf-local-term-locality` via the imported determinant-calculus chain. The split realizes the auxiliary common-summand input in the Stacks 0FJK route; the item and new nodes carry the required `blueprint.from` data and the item’s `split_report` records that realization. The local free-base-change reflection is declared as a generic tool use because it is an existing cross-unit lemma needed only for the residue-field lift.

## What remains unfinished

No proof or Lean source was written, as required for stage 1. The two Mathlib leaves remain leaves; the item is otherwise fully split.
