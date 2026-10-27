# Stage-1 delivery: lem-sfb-split-torus-subgroups-diagonalizable

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-subgroups-diagonalizable.json: item, split into five steps; no Mathlib match for the whole group-scheme statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-coalgebra-group-like-independent.json: statement, Mathlib leaf `linearIndepOn_isGroupLikeElem`, Mathlib/RingTheory/Coalgebra/GroupLike.lean:103, also indexed form at 157.
- citations.json: exact statement quotations for every proof-step citation.
- report.md: this report. searches.jsonl is the search tool's original log; prepare.py is sandbox-only preparation code, not a delivery node.

## Attachments

None. Searches of lean/WeilConjectures for the item identifier, diagonalizable/diagonalisable, group-like/groupLike, and torus found no project declaration giving the item. Mathlib's coalgebra theorem is recorded as a leaf, not a project attachment.

## Wanted literature

None. The required Milne book is present.

## Corrections and unfinished work

The imported node had no proof. I added the actual coordinate-algebra argument rather than introducing a node restating the subgroup theorem. The statement's mathematical assertions and hypotheses are unchanged. Its unused smoothness, connectedness and finite-type convention sentence was removed (it imposed no such hypothesis); the multiplicative group, affine spectrum, tensor algebra and finite-dimensional vector-space references now name the notions actually used. Corresponding statement dependencies were adjusted. There is no statement dispute. All existing provenance and blueprint fields are retained.

The new leaf states only coalgebra independence, with coalgebra and group-like spelled out; it does not assert diagonalizability, a Hopf quotient classification, or the finite-coordinate-algebra conclusion. No unsplit supporting theorem remains in this delivery. The existing geometric-criteria node is used only for its stated identification D(Z^r) = G_m^r, not its proof or geometric criteria. Its dependencies do not include this item. The item's nearest blueprint ancestor command reports None, as in the existing blueprint.from.node; new provenance preserves that value and prepends the item to via.

## Not duplicates

lem-sfb-coalgebra-group-like-independent vs lem-sfb-group-algebra-group-like-basis: the existing node characterizes group-like elements of a group algebra as its monomials; the new leaf proves independence in an arbitrary coalgebra, including the quotient algebra B before it is identified with a group algebra.

lem-sfb-coalgebra-group-like-independent vs lem-sfb-affine-group-coordinate-hopf: the existing node constructs the coordinate Hopf operations and states their identities; it does not assert independence of group-like elements.

lem-sfb-coalgebra-group-like-independent vs lem-sfb-graded-primitive-product: the existing node concerns products of degree-one primitive elements in a connected graded bialgebra, not group-like elements of a coalgebra. Its search results mention the independence theorem without stating it.

lem-sfb-coalgebra-group-like-independent vs lem-per-log-regular-chart-monomial-tor: that node concerns monomial logarithmic charts and Tor, not arbitrary coalgebra group-like independence. Its search metadata contains the declaration name but its statement does not.

lem-sfb-coalgebra-group-like-independent vs lem-weil-independent-family-card-le-dimension: the existing node bounds the cardinality of a family already assumed independent in a finite-dimensional space; the new leaf supplies independence without a finite-dimensionality assumption.

The full DAG was searched by group-like/groupLike, coalgebra, the exact Mathlib names, and Proposition 4.23, and the blueprint-reference search returned no match for group-like, coalgebra, diagonalizable, or linear independence. The new id was absent. No Stacks tag is attached to the new leaf: its actual source is Milne Proposition 4.23 and Mathlib, not an invented Stacks reference.

## Review by Q64

I read Milne Algebraic Groups (2017), printed pp.233-234, Theorems 12.8 and 12.9(c), and p.236, Definitions 12.14 and 12.17. The subgroup proof explicitly says the surjective coordinate Hopf map carries the spanning group-like elements to group-like elements; Theorem 12.8 then invokes independence to obtain a basis and a group algebra. I also read the independence proof in Proposition 4.23, printed p.93. For the new node I read Mathlib/RingTheory/Coalgebra/GroupLike.lean, the definition at lines 37-41, the theorem's domain and torsion-free hypotheses at 98-103 and the indexed form at 156-158. A field is a domain and its vector spaces are torsion-free, so this is exactly a specialization, with no finite-dimensional, Hopf, or reducedness assumption added. All searches recorded for the new node ran via msearch.py and their real answers are in searches.jsonl. LeanFinder, Loogle and LeanSearch returned the theorem, and the logged grep gives the file and lines. Two different searches of the entire item returned only related operations or general scheme results, which do not state its conclusion.

For step 1 I opened the statements of diagonalizable-group-geometric-criteria, def-weil-closed-immersion, and affine-group-coordinate-hopf. The first explicitly identifies D(Z^r) with G_m^r including r=0; the second explicitly gives affine quotient rings and surjectivity; the third states all the Hopf identities without assuming reducedness or smoothness. The map q is compatible with them because the closed inclusion is a group homomorphism: this follows by pulling back the defining three compatibility diagrams, and the step writes all three identities. No theorem about a scheme-theoretic image or a geometric-point subgroup is being substituted.

Step 2 uses the equalities proved in step 1: q(e_a)q(e_-a)=1. Thus its image is an actual subgroup of B's units; addition in M is multiplication of those units. It is generated by the r images of the standard lattice generators. Surjectivity of q and finite grouping of monomial terms prove spanning explicitly. This is a routine construction, not a hidden character-duality theorem, so it stays an elementary step.

Step 3 cites the new leaf's assertion of independence of distinct group-like elements. The coalgebra hypotheses are exactly the identities in the coordinate-Hopf node used in step 1, and the u_m are pairwise distinct by the definition of M as an image subset, not by injectivity of the original lattice map. I checked the leaf does not silently replace the quotient by a reduced algebra.

Step 4 uses the spectrum correspondence statement and the affine fibre-product statement, both read in full. The former gives contravariant algebra/scheme maps and uniqueness; the latter identifies the product with the spectrum of the tensor algebra with the stated inclusions. The step gives the linear map, its bijectivity from the basis, its multiplicativity, and the three Hopf compatibilities on the basis, so the resulting scheme isomorphism respects the group law, identity and inverse. This is the elementary assembly of previous steps, not a new unsplit classification assertion. No further fact about antipodes or group-like inverses is needed: inverse basis elements already come from e_-a.

Step 5 cites the existing Mathlib leaf independent-family-card-le-dimension. Its statement applies to any finite independent family in the finite-dimensional vector space B, so choosing d+1 distinct indices contradicts its exact inequality. The remaining multiplicative-type sentence is the inline definition in the item, since the base F is already algebraically closed.

I tested r=0 (M=0, B=F, K trivial), K trivial for arbitrary r, the whole torus (M=Z^r), roots of unity mu_n (M=Z/n), and mu_p in characteristic p. In the last case the basis 1,t,...,t^(p-1) remains linearly independent although the coordinate ring has nilpotents: this confirms why no argument using only F-points or reducedness would suffice. The new coalgebra statement also handles the zero coalgebra (no group-like elements), the one-dimensional coalgebra (the single element 1), and group algebras of arbitrary, even infinite, groups. No new node is elementary or a clause of the item; the one new node isolates the cited non-elementary independence theorem. All steps are under 2000 characters, all new node proofs are empty, and each citation quote was copied verbatim from the cited statement. No unit or chapter route was changed; no Lean file was written or compiled, and no source repository file was changed.
