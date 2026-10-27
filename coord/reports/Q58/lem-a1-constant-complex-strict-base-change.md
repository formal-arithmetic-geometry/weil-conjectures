# Q58: lem-a1-constant-complex-strict-base-change

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-constant-complex-strict-base-change.json`: statement, split into seven proof steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: 23 verbatim excerpts, one for every step/node citation.
- `searches.jsonl`: preserved command-generated Mathlib search log; five searches run by this worker (LeanFinder twice, Loogle, grep, LeanSearch).

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and the constant-complex/pullback/tower concepts. `AlgebraicGeometry.ProEtale.constantSheafCompUpperStarIso` in `SixFunctors/ProEtale/GaloisEvaluation.lean:164` supplies a constant-sheaf comparison, but does not state the full quotient-complex tower, balanced reductions, normalized units and augmentation of this item. The monoidal pullback declarations likewise cover ingredients, not the entire item. No attachment is claimed.

## WANTED

None. The relevant Stacks source files are present locally.

## Corrections and provenance

The item was unsplit, with no previous sandbox node or report. Its existing Q49 searches and every other field were retained. I clarified the sentence attributing exactness to finiteness: exactness follows from geometric inverse image and the coefficient isomorphism, independently of finiteness. This is a correction of the stated reason, with no change to hypotheses or conclusion. I made explicit the semilinear nature of tower transitions, restriction of each finite level along its completed-coefficient projection, and the strict cone convention. There is no statement dispute or change of route.

The chapter and unit records were read. This is an auxiliary scalar-comparison argument beneath `lem-a1-finite-map-purity`, not the unit's key theorem, so no unit realization fields were changed. The current main-20261015 blueprint node has the same finite-etale purity statement; the detailed scalar-complex argument is an agent-written refinement below its existing ancestor chain. The inherited blueprint provenance is retained, and the blueprint-wide searches found no equivalent whole-item node.

## Not duplicates

There are no new nodes. Existing arbitrary constant-module preservation, exact module inverse image, and the normalized pro-etale tensor comparison were reused. The similarly named `lem-a1-balanced-finite-tower-generator-comparison` concerns completed coefficients, Koszul towers and a valuation-ring datum, whereas this item starts with arbitrary scalar complexes over a general ring and proves their constant-model quotient-tower comparison and augmentation; I do not create a competitor for either statement.

## What remains unfinished

No part of this item's split remains unfinished. Its cited nodes remain independent DAG work; no Lean was written or compiled. The required server dry run and direct delivery are performed after this report is written.

## Review by Q58

I read Stacks `sites-modules.tex`, Tag 03EL (`lemma-tensor-product-pullback`), including its bilinear-adjunction proof, and the sheaf tensor construction/universal property of Tag 03EK (`section-tensor-product`). I read the constant-sheaf universal property in `sites.tex`, Tag 0H7J (`example-constant-sheaf`), and the algebraic-structure inverse image of Tag 00YV (`proposition-functoriality-algebraic-structures-topoi`), including its fixed-ring scalar endomorphisms. For the final steps I read `derived.tex`, Tag 015F (`lemma-right-derived-exact-functor`), Tag 014E (`definition-cone`) and Tag 08TC (`definition-derived-limit`), and the scalar extension adjunction in `sites-modules.tex`, Tag 03CZ (`lemma-adjointness-tensor-restrict`). These sources justify the ingredients; the strict quotient/unit calculations are explicitly marked as agent-written. There are no new-node sources to review.

In step 1 I opened the statements of `lem-pe-constant-left-module-inverse-image`, `lem-sfb-geometric-inverse-image-constant-module` and `lem-pur-proetale-inverse-image-tensor-comparison`. The first gives canonical constant-ring transport and exactness for arbitrary rings; the second gives arbitrary constant modules and naturality in every scalar linear map; the third gives an invertible tensor comparison on the specified inverse-image generators for an arbitrary scheme morphism. In particular I did not use the narrower similarly named lemma that assumes a scheme isomorphism. The sites here are the specified small sites, and the scheme morphism supplies the required geometric morphism.

Step 2 uses those constant-module and tensor naturality statements, with the tensor definition for local generators. The differential and quotient maps are R-linear, even though the quotient transition changes the level coefficient ring. I checked the two formulas explicitly and included naturality for every scalar chain map. Inverses commute with transitions by cancelling the level isomorphisms, so this is an isomorphism of strict towers, not only separate level isomorphisms.

Step 3 uses the exactness assertion of the first lemma and the actual unbounded exact-functor localization statement of `lem-weil-pbc-exact-functor-derived-factorization`. The latter says every complex represents the induced derived functor. This avoids imposing K-flatness or boundedness on the initial scalar complex. Its citation excerpt quotes that precise conclusion; the exactness citation quotes the exactness assertion.

Step 4 uses the sheaf tensor definition, the bilinear universal property explicitly supplied by `def-weil-pbc-ringed-tensor-section-calculus`, and the coordinate projections in `def-pur-sheaf-inverse-limit`. I checked balancing over both rings and both composites of the displayed inverse. Thus the reduction map needs no finite-free splitting, and no new lemma restating a clause was introduced.

Step 5 uses the same constant-module and tensor isomorphisms and the inverse-limit universal property. The coefficient map is constructed from the compatible projections; the argument does not commute inverse image past a limit. The ordinary completed-coefficient tensor comparison is obtained directly by reassociation and the two inverse balanced formulas. The reduction square is checked on its full generator including the outer scalar b'; projection compatibility gives the exact displayed equality. No flatness or invertibility of the completed-coefficient map is required.

Step 6 uses the tensor-section node's actual scalar unit formula, not merely a definition of an adjunction. I computed the quotient square, the unit case a=1, and the geometric normalization from step 5. The inverse-limit statement gives the projection-transition equality used. Replacing p by dp or f(p) checks differential and chain-map compatibility without invoking an unquoted coherence theorem.

Step 7 uses the strict Roos definition, the explicit cone and shift convention in `def-weil-abstract-derived-category`, the component equation in `def-weil-tower-transition-endomorphism`, and `def-pc-sheaf-restrict-scalars`. I checked the sign: in coordinates (y,x), the shifted cone differential is (-dy-ux,dx); hence (0,alpha) is a chain map exactly when u alpha=0. The proof gives this zero component by component. It claims no derived-product comparison or preservation of products by inverse image.

I checked zero scalar complexes, zero differentials, I=R (all finite levels and their limit zero), I=0 with R finite (the constant tower), the empty scheme, and arbitrary nonflat scheme morphisms. All formulas remain defined and valid, including units over the zero ring. The bounded finite-projective hypothesis is retained for the requested special case, although the balanced identities themselves require neither projectivity nor boundedness.

All seven proof steps are below 2,000 characters. The non-elementary comparison and derived-localization facts are cited; the other steps are the written balancing, naturality and cone calculations. The three off-unit statement tools are declared in `split_report.tool_uses`: each is a generic topos tool and replaces no step of the unit's Fourier/weight route. I verified each citation quote is copied literally from its node's statement. The inherited searches are preserved; this worker's recorded queries agree with `searches.jsonl`. The hits I read concern free module sheaves, scalar quotients, or composition of constant sheaves, not a one-line specialization proving this whole item.
