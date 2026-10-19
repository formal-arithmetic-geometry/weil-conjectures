# Worker report

Files written: the item `lem-trf-fppf-integral-surjective-refinement` and five statement nodes `lem-trf-fppf-local-finite-free-refinement`, `lem-trf-integral-surjective-open-extension`, `lem-trf-affine-infinite-product-existence`, `lem-trf-infinite-product-surjective`, and `lem-trf-infinite-product-integral`; two Mathlib leaves `lem-trf-integral-morphism-composition` and `lem-trf-surjective-morphism-composition` were also recorded. The first five are unsplit statements; the last two are exact Mathlib matches. `citations.json` records the statement excerpts used by each proof step.

Attachments: none. No declaration tagged `(blueprint: lem-trf-fppf-integral-surjective-refinement)` or matching the Stacks statement exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

WANTED: none.

No statement correction was needed. The imported item is exactly Stacks Tag 0CNZ and retains its allowance for arbitrary schemes, small families, and empty cases. The existing finite-refinement node cites this item as its first step; the new nodes are the independent inputs used by the 0CNZ proof and are not restatements of the target. Searches of the whole DAG for Tags 05WN, 0CNX, 0CNI, 0CNJ, and 0CNK and for the corresponding integral-product and fppf-refinement phrases found no duplicate statements.

## Review by N6

I read the item against `literature/stacks-project/more-morphisms.tex`, Tag 0CNZ, including the preceding Tag 05WN construction and the extension lemma Tag 0CNX. I also read `limits.tex` Tags 0CNI, 0CNJ, and 0CNK. Step 1 uses exactly the two-level finite-locally-free refinement stated by the new 05WN node; its hypotheses are precisely that the family is fppf. Step 2 applies the 0CNX extension twice, first over each $U_j\subset X$ and then over each $W_{j,k}\subset W_j$; the restriction and surjectivity/integrality clauses match the node statement. Step 3 checks that the extended maps are affine because they are integral, so 0CNI supplies both products; 0CNJ and 0CNK give surjectivity and integrality at each product level, while the Mathlib composition leaves supply the composites over $X$. Step 4 uses inverse images of the open subschemes $T_{j,k}$ to form an open cover; the pointwise choice of $j$ and $k$ is exactly the argument in 0CNZ, and the factorization through a member of the original fppf family is inherited from 05WN. Step 5 handles empty schemes and empty indexing families explicitly and checks that no quasi-compactness or finiteness condition has slipped into the conclusion. I checked the identity cover, an empty base, and a singleton affine fppf cover as small cases. Every non-elementary input is cited in the proof and in `citations.json`; the only elementary step is the empty-case bookkeeping.

## Not duplicates

lem-trf-integral-morphism-composition vs def-weil-finite-integral-morphism: the existing node only defines integrality of one morphism; this node states closure under composition and is used to compose two extensions.
lem-trf-integral-morphism-composition vs lem-weil-pbc-finite-over-field-affine-finite-dim: the existing node concerns finite morphisms over a field and affine finite-dimensional targets, while this node concerns arbitrary integral morphisms of schemes.
lem-trf-integral-morphism-composition vs lem-weil-pbc-spec-finite-ring-map-finite: the existing node is a ring-map finiteness criterion on affine spectra, while this node is composition of arbitrary integral scheme morphisms.
lem-trf-integral-morphism-composition vs lem-weil-pbc-spec-integral-ring-map-integral: the existing node is an affine ring-map integrality statement, while this node is composition of arbitrary integral scheme morphisms.
lem-trf-surjective-morphism-composition vs def-weil-surjective-morphism: the existing node defines surjectivity of one morphism; this node states that surjectivity is preserved by composition.
