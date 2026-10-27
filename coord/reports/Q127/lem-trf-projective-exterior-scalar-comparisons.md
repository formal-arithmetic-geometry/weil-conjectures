# Stage-1 delivery by Q127

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-projective-exterior-scalar-comparisons.json`: item, split; statement and statement dependencies unchanged; eight explicit proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-exterior-power-universal-property.json`: statement, exact Mathlib leaf `exteriorPower.alternatingMapLinearEquiv`, `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean:212`; the generator equation is at line 228, uniqueness at line 206.
- `citations.json`: one verbatim statement quote for every citation of every step.
- `searches.jsonl`: actual msearch results, retained without editing. Two task-local writing scripts and this report also reside in the sandbox; no repository or launcher file was written.

One new node, one Mathlib leaf, no unsplit new nodes. The new node states the alternating universal property for arbitrary modules; it does not state a scalar-extension comparison, dual comparison, determinant comparison, or any clause of the item.

## Attachments

None. Searched `lean/WeilConjectures/` by the item tag, exterior/scalar/projective notions, and the likely dual/base-change terminology. The project files contain specialized localization and sheaf comparisons, not every clause of the item. Mathlib's `IsBaseChange.toDualBaseChange` was read in `LinearAlgebra/Dual/BaseChange.lean:111-145`: it assumes `Free R V` and `Module.Finite R V`, so it is not an exact finite-projective attachment or a whole-item leaf. Its tower equation `Module.Dual.baseChange_baseChange` is also insufficient for the determinant claim. The universal-property declaration is Mathlib, not an attachment to the item.

## WANTED

None. All sources used are available locally.

## What was wrong or incomplete

The item had a statement and prior search records but no proof. Its statement is mathematically correct, so I made no statement correction. In the proof the displayed dual formula writes the image of a scalar under the ring map explicitly. The determinant definition is the exterior-algebra socle, while a general nonflat tensor functor need not preserve annihilators: the proof constructs a map landing in the socle and proves it is an isomorphism on free charts. It never assumes that tensor commutes with kernels. Likewise the short exact sequence remains exact under scalar extension because the quotient is projective and the sequence splits, not because the new ring is flat.

The nearest blueprint ancestor in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` has the contracting-correspondence argument. I read that current file and the current chapter and unit records. This item is the already-selected lower module auxiliary to the affine two-term determinant on the existing long stable-modification branch; I did not change or replace the chapter/unit route. The item is not the key statement of the unit, so no unit record is written. The item retains its existing blueprint ancestry, and the new leaf extends that ancestry through this item. Blueprint searches for exterior, exterior universal, universal alternating, 00DM, base change exterior and determinant scalar produced no universal-property node. The determinant-line representation nodes and the sheaf exterior nodes are different objects, as recorded below.

## What could not be finished

Nothing within this stage-1 item. No Lean statements or proofs were written or compiled. Downstream existing unsplit dependencies remain their owners' items.

## Review by Q127

I read Stacks `algebra.tex` Tag 00DM (`section-tensor-algebra`), including the tensor-algebra quotient defining exterior powers and the finite-free wedge basis; Tag 00NX (`lemma-finite-projective`), including its finite-free retract characterization; and Tag 00EK (`lemma-cover-module`), including the exact sequence and its proof. For the determinant I read `more-algebra.tex` Tags 0FJ9 (`section-determinants`), 0FJA (`remark-determinant-as-socle`), and both constructions in 0FJB (`lemma-det-ses`), plus `perfect.tex` Tag 0FJY (`remark-functorial-det`). Tag 0FJB omits well-definedness details and Tag 0FJY says pullback compatibility is clear from the affine construction; neither is treated as a ready-made proof. I wrote out the needed affine comparisons. The proof is marked agent-written, with these source places, because it fills those omitted details rather than pretending the source prints the calculations. No SGA source is used.

For the new leaf I read the Mathlib source at `LinearAlgebra/ExteriorPower/Basic.lean:203-236`. `alternatingMapLinearEquiv` is precisely the universal property, its inverse is precomposition, and the generator equation and uniqueness are supplied by the two displayed lemmas. The wedge convention is the same submodule of the exterior algebra as in the existing definition. I ran LeanFinder, LeanSearch, Loogle and source grep through msearch; all returned real hits. The complete original query/result summaries and digests are in `searches.jsonl`; the node records exactly those queries. The first general search wording for the item and the second scalar-comparison wording were both examined. I did not infer absence from a failed or empty service.

I opened the statement of every cited node. Step-by-step checks follow.

1. `def-weil-pbc-module-tensor-product` gives balanced universality, spanning pure tensors and functoriality; `def-weil-pbc-projective-module` gives the retract formulation. The item itself assumes a retract of a *finite* free module. The tensor constraint formulas have displayed mutual inverses; coordinate maps give B^n. Preservation of the retract follows from tensoring its two inverse equations. No flatness or finite-localization claim is taken from the definition. This is a direct calculation, not a new lemma to be queued.
2. The same two definitions suffice for the explicit finite-frame inverse. From pi=1, I derived both v=sum lambda_j(v)v_j and lambda=sum lambda(v_j)lambda_j. Substitution then proves both inverse equations. The frame is not a basis, and no assertion that a projective module is free is used. This short retract computation has no auxiliary existence assumption or concealed base-change theorem.
3. The new leaf supplies the alternating extension and uniqueness, while the existing tensor and exterior definitions give balancing, pure generators and wedge antisymmetry. I checked the inverse formula on the tensor relations, then proved alternation on *arbitrary sums*, pairing the unequal-index terms and killing the diagonal terms. This is necessary in characteristic two. The extension in both directions and their composites are written out, including r=0. The new leaf is strictly smaller than the item and is already in Mathlib.
4. The tensor/exterior definitions provide spanning sets and functorial generator formulas. The previous constructed maps are checked by substitution on f(v), mu(f(v)), the evaluation scalar bc, concatenated wedge tuples, and the tower coefficient c beta(b). Both sides are written explicitly, so no unproved 'transport' or compatibility assertion is substituted for the argument. Dual naturality uses precomposition, not the covariant action. Symmetry here is ordinary tensor symmetry, without a graded sign.
5. `def-trf-projective-determinant-module` states the annihilator model and the exterior algebra map for a ring homomorphism. The other two definitions supply the wedge and tensor balancing. I checked annihilation against 1 tensor v and then all sums c tensor v, so the map into the B-socle exists before invertibility is asserted. This argument does not extract data or a theorem from the definition's proof.
6. `lem-weil-pbc-finite-projective-standard-free-cover` gives the finite unit-generating free cover for the assumed finite-projective module. `lem-trf-projective-determinant-chart-descent` says the socle's localizations are top wedges, includes further localization and zero charts, and so supplies exactly the two chart identifications used. `lem-weil-pbc-cover-module-exact` says compatible module elements glue uniquely and an element vanishing on every chart is zero. I use it over B with the images g_a of f_a: the same equation sum a_a f_a=1 maps to B, hence they generate its unit ideal. I did not ask chart descent to assert arbitrary nonflat scalar extension. The tensor chart identifications are given with inverse fractions. The local inverse family agrees on overlaps because both maps invert the same s. Gluing elements by cover exactness gives a global linear inverse; linearity and inverse identities use uniqueness/equality detection. These are direct applications of the cited statements.
7. The socle definition gives the annihilation predicate, and chart descent gives D(0)=R with the empty-wedge normalization. Since f is an isomorphism, every target generator is f(v); this is exactly why the exterior map restricts to the socle here. The previously checked naturality and tower equations then restrict. The zero determinant comparison is multiplication, not a scalar chosen up to a unit.
8. `lem-weil-pbc-ses-projective-quotient-splits` supplies the section of p, with projectivity of W assumed. I gave the direct-sum isomorphism and its inverse and tensor their inverse equations, proving that i_B is still injective. The free-cover node applies separately to U and W; multiplying their cover elements gives a simultaneous unit-generating cover. The split decomposition makes V free on this cover. `lem-trf-projective-determinant-exact-sequence` states the kernel-first lift formula and its localization compatibility, including ranks zero: it is exactly the formula used, not merely existence of some determinant isomorphism. On the extended chart, the images of t(w_j) remain lifts. Both maps send the displayed wedge tensor to the same ordered wedge. Tensor symmetry/associativity were fixed in step 1, so the compared square has the correct source. `lem-weil-pbc-cover-module-exact` then detects equality of the maps by applying its elementwise injectivity clause to their difference. This proves the actual scalar compatibility and preserves the kernel-first ordering and signs.

I checked small cases: r=0, r=1, r greater than a free rank, V=0, U=0, W=0, A or B the zero ring, characteristic two, a nonflat quotient A->A/I, and a product ring with different ranks on the components. Empty wedges give multiplication; the r>rank exterior inverse is the unique zero map, no basis cancellation is used; the zero ring causes no rank-uniqueness argument. Product-ring ranks are handled chartwise. In a nonflat quotient the retract equations and split exact sequence persist. All steps are shorter than 2000 characters (the longest is 1359), and I checked each for an inline hidden lemma. The exterior inverse, dual inverse and wedge compatibility are the arguments of the item itself, not assertions moved into new nodes. The only missing general theorem was the alternating universal property; it is the one new Mathlib leaf.

I also checked delivery-errors B1-B10 (self-contained leaf, one-degree universal property, source tag/label, actual searches and exact file lines, ancestry, no exact project attachment), C1-C8 (every substantial external fact has a node, every cited statement read, no proof-body citation, no merged pointers or circular dependence, generic off-unit tools declared), D1-D5 (no clause cloned into a child, explicit inverses and coherence calculations, omitted source details supplied), and E1-E7 (all hypotheses in force, actual socle objects and actual maps, no implicit flatness, small cases). `proof_deps` is exactly the union of uses; every entry of citations.json is copied verbatim from the cited statement. Statement and all maintainer fields are retained. The three off-unit statements are declared as generic tool uses in split_report; they do not replace the unit route.

## Not duplicates

The following are the existing DAG files found by the common source tag 00DM. Each comparison was checked by reading its statement; sharing the tensor-algebra section does not make its theorem the alternating universal property. Other concept searches identified sheaf exterior powers, localization comparisons, finite-free wedge bases, and determinant constructions; none states the arbitrary-module universal property.

lem-trf-exterior-power-universal-property vs lem-trf-line-quotient-homogeneous-fraction-map: existing statement is "The morphism from a line quotient by homogeneous fractions"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-trf-framed-symmetric-twist-comparison: existing statement is "Framed tensor twists of the symmetric algebra"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-trf-split-exterior-comparison-localization: existing statement is "Split exterior comparison with lift independence and localization"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-trf-projective-determinant-chart-descent: gives the socle determinant and chart descent, rather than linear extensions of alternating maps.

lem-trf-exterior-power-universal-property vs lem-trf-koszul-augmentation-kflat-model: existing statement is "The augmented Koszul resolution computes the derived scalar-extension counit"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-trf-positive-copy-graded-quotient: existing statement is "Quasi-coherent positive-copy graded algebra and symmetric quotient"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-trf-symmetric-proj-tautological-chart-gluing: existing statement is "Tautological degree-one quotient charts, restriction and free comparisons"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs new-v2-exterior-power-localization: compares exterior powers under localization, rather than the arbitrary-module alternating universal property.

lem-trf-exterior-power-universal-property vs lem-sc-exterior-sheaf-local-free-comparison: existing statement is "Local finite freeness and section comparison for exterior sheafification"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-sfb-cofactor-local-descent: existing statement is "Local descent and uniqueness of the projective cofactor map"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-sfb-sheaf-rees-symmetric-presentation: existing statement is "Affine presentations and symmetric-algebra surjection for the sheaf Rees algebra"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-sfb-plucker-chart-classifying-bijection: existing statement is "Classifying maps from normalized quotient charts and determinant-line identification"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-sfb-two-term-cofactor-naturality: existing statement is "Cofactor maps are natural for derived isomorphisms of two-term projective complexes"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-cotangent-complex-symmetric-algebra: existing statement is "The naive cotangent complex of a symmetric algebra is the image of K tensor C; its differentials are M tensor C"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-finite-presentation: existing statement is "The symmetric algebra of a finitely presented module is a finitely presented algebra, generated by generators of the module"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-images-module-colimit: existing statement is "Symmetric algebra images of a finitely presented module system cover affine sections"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs stage3-graded_degree_one: existing statement is "The degree one image is the range of iota"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs stage3-graded_span_pure_tensors: existing statement is "Each image of a tensor power is spanned by products of iota"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs def-weil-pbc-koszul-complex: existing statement is "Koszul complex of a finite sequence of ring elements"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-free-module-polynomial: existing statement is "The symmetric algebra of a finite free module is a polynomial ring"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs def-weil-pbc-exterior-algebra: defines the quotient, graded pieces and pure-wedge span; does not state the universal bijection with alternating maps.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-base-change: existing statement is "The symmetric algebra commutes with base change"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs stage3-graded_kernel_internal: existing statement is "DirectSum.IsInternal of the homogeneous kernel components"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-universal-property: existing statement is "The symmetric algebra of a module and its universal property"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-degree-exact: existing statement is "Exactness on each graded piece of the symmetric algebra of a quotient"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-differentials: existing statement is "Differentials of an arbitrary symmetric algebra"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs stage3-graded_image_mul: existing statement is "Products of image components have additive degree"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-exterior-power-free-basis: gives a finite-free wedge basis, rather than the alternating universal property for arbitrary modules.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-tensor-algebra-graded: existing statement is "The tensor algebra is graded by the tensor powers"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs stage3-graded_degree_zero: existing statement is "The degree zero image is the span of one"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-quotient-module: existing statement is "The symmetric algebra of a quotient module is the quotient of the symmetric algebra by the ideal generated by the kernel"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-finite-projective-smooth: existing statement is "The symmetric algebra of a finite projective module is smooth"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-quasi-coherent-symmetric-algebra-core: existing statement is "QuasiCoherentSymmetricAlgebraCore"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-weil-pbc-symmetric-algebra-graded: existing statement is "The symmetric algebra is graded by the images of the tensor powers"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs stage3-graded_image_internal: existing statement is "The images of tensor powers form an internal direct sum"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs lem-pur-vector-bundle-finite-type-frames: existing statement is "Finite-type affine frames and purity-domain geometry for a vector bundle"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

lem-trf-exterior-power-universal-property vs def-weil-coefficient-cohomology-modules: existing statement is "Cohomology modules of a coefficient complex"; it concerns its stated construction/comparison, not the bijection Hom_R(exterior^r M,N) with all alternating multilinear maps for arbitrary M,N.

The item itself is not a duplicate of the new leaf: it compares scalar extension, duals, socle determinants, and kernel-first exact-sequence maps; the leaf compares maps out of a fixed exterior power. The existing `lem-pod-perfect-dual-scalar-calculus` already gives dual comparison for bounded finite-projective complexes; I did not create a dual-base-change node. The shorter retract calculation here proves the item's formula directly without importing its derived-category notions. The existing determinant chart-descent and split-exterior-localization nodes were reused rather than duplicated; the latter's statement is limited to localization, whereas arbitrary A->B is handled by the item's explicit formulas.

## Validation

Server review_split/check_dag and the required delivery dry run are run through the launcher tools. Their final outcome is recorded after the process exits. No local checker or compiler is run.

First full dry run returned only a missing dedicated `mathlib_match.line` field on the new leaf; the verified line was already in its source/how text. Added `line: 212` and reran. The preliminary server review_split passed.
