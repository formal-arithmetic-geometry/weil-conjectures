# Stage-1 delivery: lem-sfb-unit-framed-algebra-smooth-groupoid

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-unit-framed-algebra-smooth-groupoid.json`: statement, split into nine steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged. No new nodes or Mathlib leaves.
- `citations.json`: 26 entries, one per step/node citation, checked as literal substrings of the current cited statements.
- `searches.jsonl`: six actual searches made with msearch.py for this item. The inherited searches remain in the node as historical records. `prepare.py` is sandbox-only preparation, not a project change.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by unit-framed algebra, framed algebra, FAd, and algebra/groupoid terms found no complete project declaration. The tensor-frame coordinate file concerns morphisms of framed sheaves, not algebra laws or this groupoid.

## WANTED

None. All sources used are present locally. No SGA source is used.

## Problems in the imported item and changes

The node was statement-only. Stacks `criteria.tex`, Tag 05YP (`lemma-represent-FAd`), gives its coordinate construction and the point-groupoid identification but omits the action verification. Its paragraph asserting smoothness of the stabilizer is justified here by the determinant-open description, rather than by treating an arbitrary closed subgroup of a smooth group as smooth. The action is a right action in the first displayed argument: `a(h,a(g,m))=a(gh,m)`. The item's stated composition order is correct; its arrows intentionally encode algebra isomorphisms in the reverse direction. No statement dispute or hypothesis change is needed.

The source initially takes the base to be Spec Z and explicitly says the general case is obtained by base change. The proof here carries out the functor-of-points argument over every S. It uses the affine-target adjunction for arbitrary T, not merely affine T, and does not assume global sections commute with arbitrary scheme base change.

The latest blueprint is `literature/blueprint/latest` pointing to `main-20261024`. I read the chapter record, unit record, current unit `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The item is an auxiliary coordinate prerequisite along its inherited finite-cover-stack algebraicity chain; it does not realize the unit's key statement, so no unit record is changed. The inherited `blueprint.from.node=null` is preserved: `blueprint_refs.py ancestor` itself returns None for this chain. The explicit existing `from.place` and `via` are retained. Whole-blueprint searches for `algebra laws`, `unit framed`, `multiplication`, and `05YP` found no node stating this result.

## Not duplicates

No new nodes are introduced. Searches of the whole DAG by 05YP, algebra laws, unit frames, affine-target adjunction, principal opens, Yoneda, determinant/adjugate identities and smoothness found the existing inputs now cited. In particular I reuse `lem-sfb-matrix-cramer-determinant-identities` for multiplicativity and `lem-weil-pbc-matrix-adjugate-identity` for inverse matrices; I do not create a new matrix-invertibility node. Polynomial quotient factorization, the associator calculation, preservation of the first column, and comparison of the two point groupoids are written as elementary calculations in the item rather than separate nodes.

## Mathlib searches

All six new searches were run with the required msearch.py command, and their full returned summaries are in `mathlib_searches` with the exact tool/query and in `searches.jsonl`. LeanFinder's first wording returned affine space, smooth algebras and manifold group notes; its second wording returned submersive algebra presentations. LeanSearch returned free-module bases and their base changes. Loogle with `"AlgebraicGeometry", "Groupoid"` returned no hits. Two source greps for algebra structure schemes, unit-framed objects, multiplication tables and smooth groupoids returned no hits. These do not state the item. The useful broad notions already have existing DAG nodes and are cited there; no new Mathlib leaf is claimed.

## Unfinished work

None for this one-level split. Its existing prerequisite nodes keep their own current stage states. No Lean source was written and no compiler, Lake command, or local project checker was run.

## Review by NI

I read `criteria.tex` from the beginning of `section-hilbert-point`, through the equations defining the universal ring, `equation-objects`, `equation-FAd`, Tag 05YP (`lemma-represent-FAd`) and the following smoothness paragraph. The statement agrees with those formulas, with arbitrary S introduced by the explicitly prescribed base change. Its d>=1 hypothesis is essential to the chosen unit vector and agrees with the source. I also read each of the fifteen distinct cited node statements in full, checking the actual clauses rather than relying on their names.

Step 1 uses the basis expansion in `def-weil-pbc-free-module` and the evaluation/unicity clause of `def-weil-pbc-mv-polynomial-ring`. It spells out the associativity coefficient comparison and the factorization through the generated ideal. A polynomial in the ideal evaluates to zero because it is a finite sum of multiples of the displayed relations; this needs no further quotient-algebra theorem. The unit relations give a right unit, and symmetry gives a left unit. This step is elementary after the two cited definitions.

Step 2 takes the full arbitrary-scheme bijection in `lem-weil-pbc-morphism-into-affine-scheme`, not the weaker fully faithful Spec statement, and the pairing/uniqueness clause in `def-pc-fibre-product`. Their statements give exactly the maps to X and their unique S component. Spec Z compatibility uses the unique map from the integers. This resolves the possible nonaffine-T gap in a proof that tested only affine schemes. I checked the supporting Stacks text at schemes.tex Tag 01I1 (`lemma-morphism-into-affine`).

Step 3 cites polynomial evaluation, the unique extension and its formula in `lem-weil-pbc-localization-away-universal-property`, the same affine-target bijection and fibre product, both left and right adjugate identities, and precisely the `det(AB)=det(A)det(B)` clause of `lem-sfb-matrix-cramer-determinant-identities`. These statements hold over commutative rings with no reducedness or domain hypothesis; d>=1 satisfies that last node's positive-size hypothesis. The inverse formula and the converse determinant calculation are given explicitly. I read algebra.tex Tag 00CP (`proposition-universal-property-localization`), the adjugate paragraph in Tag 07DQ (`lemma-matrix-left-inverse`), and the pinned `Matrix.det_mul` statement at Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:138. No field-only nonzero-determinant criterion is used.

Step 4 reuses affine space's actual fibre-product definition, polynomial evaluation and the arbitrary affine-target bijection to get its points. `lem-weil-pbc-basic-open-function` supplies openness and the invertible restricted section. `lem-weil-pbc-morphism-factors-through-open-subscheme` supplies existence AND uniqueness of the factorization. Locality of scheme stalk maps reflects units: an element in the maximal ideal cannot map to a unit. Conversely the locally existing inverses glue by their uniqueness. This proves the claimed point subfunctor without silently assuming an open-base-change theorem. Finally `lem-galois-yoneda-fully-faithful` really states the natural-transformation/morphism bijection, which gives the scheme isomorphism from the two inverse transformations. Its naturality respects the map to A. I checked schemes.tex Tags 01HZ (`lemma-f-open`) and 01HI (`lemma-restrict-map-to-opens`) and categories.tex Tag 001P (`lemma-yoneda`).

Step 5 uses the product universal property and Yoneda to obtain scheme operations from the explicitly natural matrix operations. It verifies the first-column condition for products and inverses and writes the associativity sum. These are computations in any commutative ring, not an appeal to an unrepresented group functor.

Step 6 uses only the product universal property and Yoneda beyond elementary ring and linear-map manipulations. It verifies the unit, symmetry and both associators, and writes the transformed coefficients. The adjugate formula was established in step 3, so naturality of inverse entries and regularity require no extra smoothness or rational-function lemma. This fills the source's omitted action check; no auxiliary node merely repeats this clause of the item.

Step 7 uses product pairing, Yoneda's injectivity on morphisms and the actual pointwise groupoid laws of `def-sfb-algebraic-space-groupoid`. The latter's statement applies to presheaves and specializes to these representable ones; its composition is c(a,b)=a after b. The calculation gives a(h,a(g,m))=a(gh,m), and hence composition ((h,m'),(g,m)) has label gh. Its two source/target clauses, both inverse laws and associativity are individually verified. In particular I did not import the usual left-action formula with the opposite order.

Step 8 takes smoothness of affine space over EVERY scheme from `sbc-lem-affine-space-smooth`, restriction and invariance under isomorphism from clauses (a),(c) of `lem-weil-pbc-smooth-restrict-open-subschemes`, and only clause (2) of `lem-pc-proper-base-change`. The latter states smoothness under arbitrary base change and does not require the base to be Noetherian or proper. Its name's proper clause is not used. The factor swap is a canonical isomorphism and the already-constructed inverse-arrow involution gives the isomorphism relating s and t. I read morphisms.tex Tags 01V6 (`lemma-smooth-characterize`), 01VB (`lemma-base-change-smooth`) and 01VC (`lemma-open-immersion-smooth`). The affine-space smoothness node and the smooth-base-change node are generic tools from other units, explicitly declared in `split_report.tool_uses`; they supply black-box properties, not a replacement of this unit's route. The restriction node is already a Mathlib leaf. Nothing asserts smoothness of the algebra-law scheme X.

Step 9 is an elementary assembly of the preceding bijections: it checks the arrow direction, identities, composition and each pullback formula. It invokes no additional node. I checked rank one explicitly: B_1=Z, determinant 1, no matrix coordinates, X=G=S. I checked the empty scheme and zero ring (there is one empty coefficient tuple, 0=1 is a unit and the matrix inverse equations remain valid); nilpotent coefficient rings (the adjugate proof uses units, not nonzero determinants); and nonaffine/disconnected T (the affine-target lemma and sheaf gluing hold without connectedness, quasi-compactness or affineness). There is no d=0 assertion. Every proof step is below 1000 characters and no long step conceals a new lemma.

Against delivery-errors B--E: no statement-only new node or hidden notion is introduced; all displayed formulas have ordinary single TeX escaping in JSON values; every non-elementary input is an existing cited statement; all 26 citation quotes were checked verbatim; no dependency uses a cited proof instead of its statement. I retained every inherited provenance/search field. The main corrections were to fill the omitted action verification, justify the determinant-open smoothness, and carry representability to nonaffine test schemes. The source and item statements themselves needed no correction.

Dry-run repair: the citation gate required at least 40 characters for the determinant-multiplicativity quotation. I replaced that short exact formula with the complete cited statement; the proof and mathematical dependency are unchanged.
