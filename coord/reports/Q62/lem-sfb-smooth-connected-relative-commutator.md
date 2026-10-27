# Q62 stage-1 delivery: lem-sfb-smooth-connected-relative-commutator

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-connected-relative-commutator.json`: statement; split in eight steps, using existing DAG nodes. Mathlib verdict: no match for the relative group-scheme theorem. Statement and statement dependencies unchanged.
- `citations.json`: eighteen verbatim statement quotations, one for each cited node in each step.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log; `write_split.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. The existing leaf `lem-sfb-geometrically-reduced-group-smooth` is used; it is not a new leaf of this delivery.

## Attachments

None for the item. Searches of the project `lean/WeilConjectures/` for the exact blueprint tag, relative commutator, smooth commutator and commutator smooth found no declaration stating the item. Source declarations about abstract commutators, curve cohomology and proper group commutativity do not meet the item. No Lean file was written or compiled.

## WANTED

None. The proof's source and the geometric inputs were available locally.

## What was wrong or changed

The imported statement is correct. Its proof was empty; I supplied the construction and all the arguments. It is essential not to claim that the rational points of the generated subgroup are the abstract commutator subgroup over an arbitrary field, or that minimality over k automatically gives minimality over every k-algebra. Neither claim is used. I use universal affine points for scheme factorization and tensor-family zero detection for relative normality.

The relative commutator image is not made inversion stable by swapping its two entries: the second entry must stay in N. The correct identity is c(g,n)^{-1}=c(g^{-1},gng^{-1}); normality of N makes this a valid substitution over every algebra. That same hypothesis supplies the simultaneous conjugation substitution used to prove normality of D.

The item inherits `blueprint.from.node = null`. The prescribed ancestor command also returns None; I preserved this ancestry and its detailed nonempty place and via list rather than inventing a blueprint ancestor. The blueprint-wide searches for `commutator`, `relative commutator` and `generated subgroup` found no blueprint node stating this theorem. The current latest blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`: its direct-image proof now uses compactification in clause (3). This supporting Milne group-theory item has no counterpart there; this delivery changes no chapter, unit or upper-level proof route.

## What could not be finished

Nothing in the stage-1 split remains unfinished. Existing cited nodes retain their own stage states; this delivery does not edit or claim to finish them.

## Not duplicates

No new nodes, hence no new-versus-existing pairs. In particular I reused `lem-sfb-affine-pointed-map-generated-subgroup` instead of creating a second generated-subgroup theorem, `lem-sfb-geometrically-reduced-group-smooth` for smoothness, and `lem-sfb-vector-space-tensor-family-zero-detection` for the conjugation argument. The existing `lem-sfb-smooth-connected-derived-subgroup` is restricted to an algebraically closed field and takes both commutator entries in the same group; it additionally identifies rational points. It is not the present arbitrary-field relative theorem. `lem-sfb-smooth-ambient-normality-geometric` could only help after establishing geometric subgroup invariance; the direct tensor calculation avoids introducing that additional premise.

## Searches and sources

I read Milne, Algebraic Groups (2017), Propositions 2.46–2.48 and 2.50, printed pp.54–56, Definition 6.24 and Remark 6.25(b), printed p.131, and the descending central series immediately before Proposition 6.38, printed p.133. Proposition 6.18, p.129, supplies the comparison with the usual derived-group normality argument; I expanded the relative conjugation calculation explicitly rather than importing a pointwise normality claim. No SGA source is used.

For the geometric hypotheses I read Stacks `varieties.tex`, Tag 04KV (`lemma-geometrically-connected-if-connected-and-point`), Tag 0385 (`lemma-bijection-connected-components`) and Tag 056T (`lemma-smooth-geometrically-normal`), and `morphisms.tex`, Tags 01VB (`lemma-base-change-smooth`) and 01VA (`lemma-composition-smooth`). The other source references are the existing finite-type clauses Tags 01T3 and 01T4 and affine products Tags 01I4 and 01JQ. The precise smooth-group leaf was checked against `Mathlib/AlgebraicGeometry/Group/Smooth.lean`, `AlgebraicGeometry.smooth_of_grpObj`, lines 64–71. I read the tensor-family theorem in `lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basis.lean`, lines 32–48; the DAG node states exactly its vector-space specialization.

The Mathlib queries were run only through the required msearch command. LeanFinder, Loogle, LeanSearch and grep all returned successfully. I read the reported abstract group declarations and the grep hits in `Mathlib/AlgebraicGeometry/Group/Abelian.lean`; they concern ordinary subgroups or commutativity of proper group schemes, not a minimal closed subgroup scheme with the required geometry. A second semantic phrasing and a narrower group-geometry grep still produced those mismatches. The exact queries and raw logged results are appended to the item's prior search records; prior records are preserved as history, not claimed to have been run by Q62.

## Review by Q62

I checked the item against Milne's relative-commutator definition and his generated-subgroup construction, rather than against a similarly named abstract group result. The hypotheses used at each stage are present: k is an arbitrary field, G and N are affine finite-type smooth connected group schemes, and N is normal. Both identity points are rational; all products are over k. No algebraic closedness, perfection, geometric irreducibility, or reduction of a test algebra is assumed.

Step 1 uses the full affine tensor-product conclusion of `lem-weil-pbc-fibre-product-affine-spectra` and both finite-type clauses of `lem-sfb-finite-type-composition-base-change`. I read their statements. Their conclusion applies to arbitrary base changes, so the products and their powers are affine finite type. The two definition nodes cited really identify affine morphisms with ring maps and closed affine subschemes with quotient rings; the factorization test is proved by descending a homomorphism, not taken from an unstated theorem.

Step 2 uses only the group operations and the pointwise definition of a normal closed subgroup from `def-sc-group-scheme` and `def-sc-group-scheme-subgroup`. I checked the inverse identity by cancellation and that gng^{-1} belongs to N(R) before using it as the second commutator entry. The universal affine point then turns conjugation into the required scheme morphism. This is an elementary substitution argument, not a separate lemma moved out of the item.

Step 3 uses specifically clause (2), not the properness clause, of `lem-pc-proper-base-change`; it states exactly smooth base change. `lem-trf-smooth-composition` states smooth composition, and `sbc-lem-smooth-geometrically-reduced` states geometric reducedness of the fibres. Over Spec k that fibre is X, so the result gives precisely the geometric reducedness needed later. I verified that the hypotheses are smoothness alone; no properness is being inferred from the title of the first node.

Step 4 uses the rational-point criterion separately on G and N; `lem-sbc-connected-rational-point-geometrically-connected` explicitly permits arbitrary field extensions. For any further field extension, `lem-weil-pbc-geometrically-connected-product-components` gives the needed bijection of components. Nonemptiness is retained by the identity points. Thus the conclusion really is geometric connectedness of X, not just connectedness over k.

Step 5 uses the statement, not the proof, of `lem-sfb-affine-pointed-map-generated-subgroup`. That statement gives the ideal intersection formula, the closed subgroup, unrestricted minimality, finite type, geometric reducedness and geometric connectedness. All its hypotheses were established in the previous steps, including inversion stability on every algebra. `lem-sfb-geometrically-reduced-group-smooth` applies since D is a finite-type geometrically reduced group scheme over a field. The joint zero detection of the induced maps follows directly from the stated intersection formula and is written out; it does not assume that an infinite intersection commutes with tensor products.

Step 6 uses exactly the unrestricted minimality clause of the same generated-subgroup node. The universal point of the affine source turns the hypothesis on all algebra-valued commutators into scheme factorization. The candidate K is allowed to be nonreduced, disconnected and nonnormal. Taking K=N is legitimate because step 2 proved its commutator containment over all algebras. No geometric-point containment is substituted for closed-subscheme containment.

Step 7 uses the actual group-operation definition and the affine product ring identification to express conjugation of every word as a morphism identity. Normality of N is checked before defining T_n. The displayed identity has the correct order of the commutator entries. Every a in I has zero pullback along every w_n, so the displayed tensor equations follow without a density or separability argument. This is an explicit calculation from the already cited construction, not a hidden invariance theorem.

Step 8 uses `lem-sfb-vector-space-tensor-family-zero-detection` with M=C and right factor A, after swapping the factors of A tensor C. The maps f_n have exactly its joint-zero-detection hypothesis by step 5. The node imposes neither finite dimension nor a finite index set, so it applies to all word maps. Vanishing on I yields factorization of the entire conjugation morphism, hence invariance on every R-point; replacing h by h^{-1} gives equality, exactly the normality definition in `def-sc-group-scheme-subgroup`. This is the substantive scheme-normality check.

I checked delivery-errors B through E point by point. There are no new statement-only node, leaf metadata, same-tag or definition-node issues; all TeX strings are singly escaped after JSON parsing. Each citation was opened and its whole statement copied verbatim into citations.json; the quotations expose its hypotheses as well as its conclusion. No step uses another node's proof. The new proof dependencies were checked for paths back to this item and none were found. The three generic off-unit nonleaf tools are declared with their precise uses in split_report.tool_uses. Each step is below 2000 characters, and none hides a separate comparison or standard argument.

Small cases checked: if N is trivial or central then every word map is the identity-valued map, I is the identity ideal and D is the trivial smooth connected normal group. This includes commutative G. Taking N=G recovers the usual derived-group construction. Dimension-zero smooth connected groups likewise give the trivial group. The proofs are unchanged over imperfect fields and for nonreduced algebras, since all factorization tests use universal affine points and the normality argument uses linear tensor detection over k. In particular no rational-point density inference is used for a nonreduced candidate K. I made no statement correction and left no disputed mathematical claim.
