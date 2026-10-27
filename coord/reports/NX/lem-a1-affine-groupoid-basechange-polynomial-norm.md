# Stage 1 report: lem-a1-affine-groupoid-basechange-polynomial-norm

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-groupoid-basechange-polynomial-norm.json`: the item, statement unchanged, now split in eight steps. Mathlib verdict: no match for the whole statement.
- `citations.json`: twenty step/node entries with verbatim statement quotations, checked against the current repository.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0. Existing nodes suffice; no elementary calculation or clause of the item has been made a new node.

## Attachments

None. Searched the project source under `lean/WeilConjectures/` for the exact blueprint tag and for groupoid/norm and invariant/norm terminology. The groupoid material found concerns descent and affine neighbourhoods, not this polynomial specialization formula. There is no project declaration giving every clause of this item.

## WANTED

None. All sources used are present in `literature/`.

## Findings and changes

The original statement is retained, including arbitrary nonflat C→D, the explicit expression-dependent polynomial formula, m=0, arbitrary local ranks, and equality of values at k-algebra points. Its proof was empty. The split supplies the invariant-base structure maps and their base changes, finite-local-freeness, polynomial invariance, and a local multiplication-matrix calculation for the actual evaluation map. In particular, the argument does not assert that invariants commute with a nonflat extension.

The invariant-norm node already states precisely the groupoid theorem needed. The polynomial-norm-invariant node was also read: its statement handles one variable, whereas the general scalar invariant-norm node applies directly to the groupoid over C[T₁,…,Tₘ]. No multivariable restatement was created. The norm-charts node only supplies local norm charts; its proof's base-change facts are NOT borrowed. Instead steps 5–7 give the explicit tensor identification, the multiplication matrices and the determinant equality.

I read the chapter and unit records and the current main-20261015 statement and proof of lem-a1-affine-hc0. The item's inherited blueprint ancestry is a historical affine-quotient branch, through the orbit-fibres item; the current support proof of affine-hc0 no longer needs that branch. I retained that provenance, described it in split_report.blueprint, and did not change a chapter, a unit, or the item statement. There is no released repair note for this item. The sandbox initially contained no item, proof or report.

## Mathlib and blueprint searches

The existing five 2026-10-22 search records were read and preserved. New searches were run only through the required msearch.py command and appended from its actual log. Both LeanFinder phrasings, LeanSearch, Loogle `Algebra.norm, TensorProduct`, and grep `norm.*baseChange|baseChange.*norm|groupoid.*norm` in RingTheory ran successfully. Loogle and grep returned zero hits; the semantic searches returned affine base-change, localization, field/ideal norm and representation-norm results. None states the groupoid polynomial scalar-image formula. I read Mathlib/RingTheory/Localization/NormTrace.lean, including Algebra.norm_localization: it assumes global freeness and localization, so does not settle this item by specialization. No service failure was reported as absence.

The ancestor command confirmed lem-a1-affine-hc0. The whole-blueprint search for `norm` and the narrower `groupoid norm` search were read; no imported blueprint node states the item. Whole-DAG searches by Tags 03BH, 03BK, 03BL and 0BD2 and by norm/base-change and determinant/base-change terminology found the existing invariant-norm and polynomial-norm nodes, norm charts and affine tensor-product/base-change nodes that this split reuses.

## Not duplicates

No new node is proposed. In particular no multivariable copy of lem-a1-affine-groupoid-polynomial-norm-invariant or base-change copy of the item is introduced.

## Review by NX

I read Stacks groupoids.tex at lemma-determinant-trick (03BH), lemma-invariants-base-change (03BK), and lemma-points (03BL), exercises.tex at exercise-trace-det-rings (02DV), divisors.tex at lemma-finite-locally-free-has-norm (0BD2), and morphisms.tex at the finite, flat and locally-finite-presentation base-change lemmas (01WL, 01U9, 01TS). There are no new-node sources to review. The scalar norm and polynomial lift follow these passages, but the stronger explicit evaluation identity and the details omitted in 03BK(1) are supplied by this agent; proof_origin therefore says agent. No SGA source is used.

For step 1 the only input is the group's given identities and C's defining equalizer. I checked the structure map on the composition domain using s p₀=t p₁, and checked identity, inverse and composition over Spec C explicitly.

For step 2 I opened def-pc-fibre-product and lem-weil-pbc-fibre-product-affine-spectra. The former states the universal property and functoriality, so maps on an H over D are exactly the maps over C needed in the original groupoid. The latter identifies the rings AND the two projections; it therefore justifies the tensor descriptions and the indicated sigma_D,tau_D, not merely affineness. No flatness is needed for either statement.

For step 3 I read all three permanence statements. Finite-morphism-permanence (a) covers arbitrary scheme base change, flat-morphism-base-change has no extra restriction on the new base, and qcqs-morphism-permanence (3) explicitly includes locally finite presentation. The definition of finite locally free is exactly finite + flat + locally finite presentation. Thus all required hypotheses hold, also when D is a polynomial ring. These facts are cited as theorem nodes, not attributed to the definition alone.

For step 4 I read the full statement of lem-a1-affine-groupoid-invariant-norm: it assumes an affine groupoid with finite locally free source and target and allows varying rank and nilpotents. Steps 1–3 give precisely those hypotheses for the polynomial groupoid. Its equality is used for the norm of the specified F. The multivariate-polynomial definition supplies coefficientwise representation and evaluation. Comparing coefficients proves membership in C[T], without a flat-invariants theorem. The displayed mutually inverse maps establish the polynomial tensor identifications directly.

For step 5 the multivariate-polynomial node gives the evaluation homomorphisms, the module-base-change node gives the balancing relations and induced maps, and the affine-fibre-product node gives the geometric square. I checked the tensor isomorphism on b, a and every T_j: the inverse respects c in C because its two copies agree, and moving a or T_j across the tensor gives exactly sigma(a) or 1⊗d_j. The target pullback of F specializes to tau_D(f).

For step 6 the norm-charts statement is used only for the existence of a cover with a finite basis and the local norm characterization. Finite-morphism-permanence (b) supplies affineness over the affine charts. The affine-fibre-product statement then gives the chart algebra L⊗E E'. I checked the basis through its inverse coordinate map, and wrote the multiplication identity after applying h to every matrix coefficient. The determinant node states the signed permutation formula, which immediately gives det(h(M))=h(det(M)); the endomorphism-determinant node identifies that determinant with the specified local norm. No norm-base-change theorem hidden in another node's proof is used.

For step 7 equality on the inverse-image chart cover is equality of sections. The only algebra afterwards is the tensor balancing identity g⊗z=1⊗d(g)z for g in C, using the stated module-base-change definition; the polynomial definition supplies the finite coefficient sum. For step 8 the scalar identity follows directly from the hypotheses that alpha₀ and alpha₁ are k-algebra maps. Algebraic closedness is preserved in the statement, although the last scalar calculation works for any field.

I checked small cases: the identity groupoid (C=A, norm the element); the pair groupoid on Spec(Z×Z) over Spec Z (norm the product of the two components), including the nonflat extension Z→Z/2 and the nonreduced extension Z→(Z/2)[ε]/(ε²); and the disjoint union of an identity groupoid and a two-object pair groupoid (different ranks 1 and 2). The matrix calculation is coefficientwise and works unchanged in these examples. For m=0 it applies to F=0 without invoking a positive uniform rank or dividing by a rank. For the zero base ring or an empty inverse-image chart, all identities hold in the zero section ring; the determinant convention for an empty basis is 1. No reducedness or global freeness has been introduced.

Against delivery-errors B–E: the item remains self-contained, all notions keep their statement dependencies, no unsplit new statement contains a proof because there is no new node, sources are identified by tags/labels, every step has an explicit argument and an elementary flag, all cited statements were opened and quoted verbatim in citations.json, and no clause has been moved into an alias node. The union of uses is proof_deps. All steps are shorter than 2000 characters; the matrix calculation is a direct calculation, not an unproved general comparison. The norm-charts tool use is declared in split_report.tool_uses for review. No SGA route or unit-route replacement is involved. The first dry run requested a longer verbatim quotation for the scalar invariant-norm citation (minimum 40 characters). I extended it to include the quantifier and the source/target equality, with no mathematical change. Server preflight/check_dag/review_split will verify graph and delivery mechanics in the required dry run.

## Unfinished work

None in this one-level stage 1 split. No Lean was written and no compiler or build tool was run.
