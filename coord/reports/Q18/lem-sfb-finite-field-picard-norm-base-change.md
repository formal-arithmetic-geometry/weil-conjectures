## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-picard-norm-base-change.json` (statement, split, not a Mathlib leaf), `citations.json`, and this report. `searches.jsonl` is the unmodified search-command log. No Lean was written and no compiler, Lake, build, or repository git command was run.

## New nodes

None. The construction uses existing DAG statements and explicit coordinate calculations; it does not move a clause of the item into a fresh node. There are zero new Mathlib leaves.

## Attachments

None. Searched the current project `lean/WeilConjectures/` both by the exact blueprint id and Picard/norm/base-change concepts. Read `FiniteLocallyFreeNormCharts.lean`, whose `exists_finiteLocallyFree_norm_charts` gives norms of regular functions on affine charts, and inspected the norm definitions in `BaseChangeNorm.lean`. These do not give a norm of isomorphism classes of line bundles, its multiplicativity, and its naturality, so neither finishes this item. The norm-chart declaration is not used as a substitute for a Picard norm.

## WANTED

None. All sources used are present.

## Findings and searches

The live item is unsplit, with an empty proof and no Lean attachment, and the sandbox initially had no item/report. Its statement is correct and is preserved verbatim, including arbitrary k-schemes and inseparable finite extensions. Read the current chapter record, unit record and latest blueprint unit in `literature/blueprint/latest/`, not a historical snapshot. The auxiliary item's `blueprint.from.node` is already null; `blueprint_refs.py ancestor` confirms there is no imported ancestor in its recorded creation chain. Retained that chain and specified the norm paragraph it realizes in its immediate parent's Picard-descent proof. This is an auxiliary calculation below the unit, not a replacement for any chapter/unit step.

DAG searches by tags 0BCY, 0BD2, 0BUT and norm/Picard concepts found the already split finite-trivialization, function-norm, norm-frame, section-norm and finite-norm-section statements. Read their full statements. In particular, `lem-sfb-finite-locally-free-function-norm` explicitly omits arbitrary base change; citing it for that clause would be C4. Instead, one fixed k-basis of K gives multiplication matrices on every scheme, and step 7 writes their entrywise pullback identity. This also avoids importing the nontrivial equivalence between two definitions of finite locally free morphism: the proof uses only finiteness of p_Z, established directly from the affine tensor-product charts.

Whole-blueprint searches `norm-invertible` and `norm homomorphism` had zero matches. The broader `finite field` search gave no norm on Picard groups. Reused the affine fibre-product and open-fibre-product nodes, rather than creating special cases. No proposed new node survived these searches, so no duplicate pairs require a new-node comparison.

Ran msearch for the item with LeanFinder, Loogle, grep and LeanSearch, then a second semantic phrasing and targeted PicardGroup grep. Read the returned declaration types and `Mathlib/RingTheory/PicardGroup.lean` lines 550–575. `CommRing.Pic.mapAlgebra` is extension of scalars in the opposite direction to the needed norm; `relPic` is a kernel subgroup. Algebra/field norms are norms of elements, and NormalEpiCategory hits are substring noise. No result states a scheme Picard norm. Queries and actual summaries were appended to the existing search records without inventing or repeating their historical searches. The targeted single-file grep output labels its first column unusually, but its contents were checked against the source itself; no declaration is claimed as a leaf on that basis.

## Not duplicates

No new nodes. Existing `lem-sfb-norm-frame-tensor-section-gluing` supplies existence of the norm cocycle line, not independence of frames or scheme pullback. Existing `lem-sfb-finite-locally-free-function-norm` is a regular-function result without the line-class base-change clause. Their genuinely additional consequences are proved in the item's steps, not packaged as duplicate nodes.

## Review by Q18

I read Stacks `divisors.tex`, section Norms (0BCX), including the full statement and proof of 0BUT (`lemma-finite-trivialize-invertible-upstairs`, lines 3617–3652), 0BCY (`lemma-norm-invertible`, lines 3655–3692), and 0BD2 (`lemma-finite-locally-free-has-norm`, lines 3789–3823). The item agrees with their construction. The degree is positive because K is a nonzero finite-dimensional k-vector space. The sources impose neither separability nor reducedness on these norms. Stacks 0BCY explicitly omits the verifications of well-definedness, additivity and the degree formula; these are now supplied by frame calculations in steps 4–6. Stacks 0BD2's base-change assertion concerns functions, so step 8 supplies the additional argument for line classes.

Step 1 uses the actual statements of `lem-weil-pbc-fibre-product-affine-spectra` (Spec of a tensor product, with both projection ring maps) and `lem-weil-pbc-open-fibre-product` (the preimages are the indicated open subschemes). I read their source in `schemes.tex`, `lemma-fibre-product-affine-schemes` (01I4, lines 985 onward) and the open-fibre-product assertion (01JR). The explicit inverse coordinate maps prove freeness using the chosen field basis; the dimension definition identifies its length with d. The finite-morphism definition requires an affine morphism with finite section algebras, and these charts give exactly that. Coordinates are glued on affine refinements of overlaps, so no assumption that arbitrary intersections are affine enters. No flatness or finite-presentation theorem is silently used.

Step 2 takes only determinant multiplicativity from `lem-sfb-matrix-cramer-determinant-identities`. Its statement allows any commutative ring and n≥1; d≥1 checks that hypothesis. I checked the cited source `Matrix.det_mul`, in the pinned Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean:138`. The determinant definition supplies the finite permutation formula; the identity/scalar cases and preservation of units are written out. The section norm is built on a global sheaf basis, so no determinant change-of-basis or choice lemma is being hidden here. A basis of K is fixed for the whole family of norm maps, which is sufficient for the existential statement.

Step 3 uses `lem-sfb-finite-trivialize-invertible-upstairs` only for a base-open cover trivializing F upstairs. F is invertible and p_Z has just been shown finite. It then uses `lem-sfb-norm-frame-tensor-section-gluing` for precisely its displayed cocycle, invertible module N and generating sections f_i. That node assumes only multiplicativity, preservation of one and restriction compatibility of the function maps, all proved in step 2. It imposes no vanishing, Noetherian, flatness or positive-power hypotheses for the existence of N. The complete statements of both nodes were read, not just their proofs or sources.

Step 4 uses clause (1) of `lem-weil-pbc-glue-sheaves-of-modules`, whose statement explicitly glues morphisms and asserts their uniqueness. I read its source, `sheaves.tex`, `lemma-glue-maps` (04TN, lines 5078 onward), including its sectionwise proof. The displayed formula v'ij=ν(ai)vijν(aj)⁻¹ checks the direction of the local maps f'i↦ν(ai)fi; multiplication by units gives inverse local maps. Common refinements handle arbitrary covers; transported frames handle isomorphic input modules. This supplies the omitted well-definedness, rather than claiming it from the norm-frame node.

Step 5 uses clauses (1)–(2) of `lem-weil-pbc-invertible-pullback-tensor` for invertibility and open restriction of tensors, and the unit isomorphism from `lem-weil-pbc-module-tensor-symmetric-monoidal` for local tensor frames. I read `modules.tex`, `lemma-tensor-product-pullback` (01CD), `lemma-pullback-invertible` (0B8L), and `lemma-constructions-invertible` (01CT). The bilinear transition equation is explicit, and the morphism-gluing node then identifies the outputs. The structure-sheaf case is checked using the actual global frame 1, not inferred from an unstated Picard-group theorem.

Step 6 uses the tensor inverse-image definition to pull back a frame and its scalar transition. The invertible-pullback node ensures it is still a line bundle. The tensor-power assertion of the norm-frame node really does state that powers have the powered transition functions; applying it with identity morphism and identity function maps verifies all its hypotheses and uses n=d≥1. Morphism gluing then gives the required isomorphism with A to the dth tensor power. No extra pullback power identity was assumed.

Step 7 reuses only the two affine/open fibre-product statements and the explicit determinant formula. I checked that the map on scalar-extended coordinate rings is r⊗x↦h♯(r)⊗x, so it preserves the same chosen K-basis. Applying a ring homomorphism to the finite determinant sum proves the desired function identity with all the maps specified. Affine source opens inside inverse images of affine target opens form a cover, even for nonseparated non-Noetherian schemes. This is a short elementary polynomial calculation, not an appeal to an uncited arbitrary-base-change theorem.

Step 8 uses the pullback definition, invertibility under pullback, and morphism gluing. The equality p_Z h_K=h p_W identifies the exact opens where the pulled-back frames live. Step 7 identifies their transition coefficients with the pulled-back norm coefficients. Thus the maps between the actual frames agree and glue; the inverse maps glue as well. This proves equality of the requested line classes and not merely agreement of fibrewise values.

The off-unit statements declared in `split_report.tool_uses` are the generic module-morphism gluing and tensor/pullback tools just described. No same-unit statement supplies their general assertions, and they replace no step of the unit's proof. I set no maintainer-owned `tool_uses` field. The two affine fibre-product facts are already Mathlib leaves.

Small cases checked: K=k (d=1) gives scalar multiplication matrices; Z empty and W empty use empty-cover sheaf uniqueness; a trivial line uses the single frame 1. For a purely inseparable degree-p extension K=k(t) with t^p=a, and even a nonreduced base algebra R, the basis 1,t,…,t^(p−1) still has the displayed explicit inverse coordinate maps. A nonflat morphism R→R/I still acts entrywise on multiplication matrices, and determinant sums still commute with that quotient. No cardinality-of-geometric-fibres or separable-product formula appears. No new statement has been introduced, and no statement correction or dispute was needed. All eight steps are under 2000 characters; none conceals a separate comparison lemma under a long-step exception. I corrected the initial temptation to cite the function-norm node for arbitrary base change by supplying the matrix computation itself.

Every node named in every proof-step `uses` has an entry in `citations.json`; each quote is copied verbatim from that node's statement, and I checked that it contains the clause the step actually uses. New-node, source, route, elementary-step, and hypothesis checks B–E were made against the files above. Nothing remains mathematically unfinished in this one-level split; the existing dependency nodes retain their own proof obligations.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/Q18/lem-sfb-finite-field-picard-norm-base-change at d9766ff2623: preflight passed`. It ran the server preflight and saved its durable receipt. After recording that result, the final dry run is repeated before the push. No local DAG/preflight/review script is run.
