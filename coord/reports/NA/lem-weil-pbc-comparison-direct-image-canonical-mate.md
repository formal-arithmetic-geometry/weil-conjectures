# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-comparison-direct-image-canonical-mate.json`: item split into five proof steps; no new nodes.
- `citations.json`: verbatim citation quotes for every step dependency.

## Attachments

None. I found no sorry-free declaration in `WeilConjectures/` stating this exact canonical mate theorem.

## WANTED

None.

## What was checked

The item source is the blueprint proof of `prop-weil-pbc-comparison-direct-image.md`, especially its first two paragraphs and the paragraph beginning “We check that the isomorphism just calculated is induced by alpha_L”. The ancestor route is the proof of `lem-weil-pbc-transport-identifies-exchange.md`. I searched the whole DAG and blueprint for the canonical mate, its counit normalization, and each ingredient; all required ingredients already have nodes, so no duplicate or auxiliary node was created. The Mathlib search log records LeanFinder, Loogle, and grep searches for the item (the generic `CategoryTheory.mateEquiv` results do not state the etale/pro-etale comparison).

Step 1 uses the existing pullback comparison node for `A_U l_u ≅ p_u A_V` and the existing adjunction-mate definition for the transpose construction; these statements explicitly provide the maps used. Step 2 uses their naturality and the mate bijection, with the naturality calculation treated as elementary. Step 3 uses the global-cohomology comparison, derived-cohomology continuity, and etale restriction-injectives nodes exactly for the three terms in the affine basis calculation; their statements provide the required hypotheses and conclusions. Step 4 uses global-cohomology comparison, pro-etale restriction-injectives, and exactness of pro-etale inverse image to identify the target derived sections. Step 5 uses comparison injective acyclicity, the comparison sections formula, basis-derived detection, and the mate definition to identify the named map, detect its isomorphism, and derive the displayed counit normalization. I checked that each citation quote in `citations.json` is verbatim from the cited node and that every proof dependency occurs in `uses`.

I also inspected the read-only slopmaster2 source. It contains the broader `comparison_derivedBaseChangeMap` theorem with `sorry`, but no declaration tagged with this item, so there is no attachment. The item keeps the finite discrete coefficient and qcqs hypotheses exactly as imported; no coefficient category was changed. Small edge cases (identity morphism and zero/identity counit) are covered by the mate definition and its triangle identities; the proof does not exclude them.

## Review by NA

I re-read every cited node before writing the split. In particular, the pullback node states the required natural isomorphism; the mate node states the bijection and transpose formula; the global-cohomology, continuity, etale/pro-etale restriction, injective-acyclicity, sections, and basis-detection nodes state respectively the exact comparisons invoked in Steps 3–5. The qcqs assumptions are used to form the affine finite-presentation stages and to invoke the imported comparison theorem, while exactness is cited where a resolution is restricted or pushed forward. I corrected the imported empty proof by making the canonical-map construction explicit, separating the affine cohomology argument from the named-map verification, and adding the normalization as the final mate identity. No new node was necessary, and no statement was weakened.


## Second reading by NA

- Item statement: compared all coefficients, qcqs hypotheses, bounded-below domain, pullback direction, transpose and counit normalization with the first paragraphs and named-map verification of `prop-weil-pbc-comparison-direct-image.md`, and the ancestor transport statement; PASS, statement unchanged. Stacks 099R is `proetale.tex`, `section-comparison`, a setting rather than a standalone direct-image theorem; 0B65 is `categories.tex`, `lemma-transformation-between-functors-and-adjoints`, whose counit square has the stated composition order.
- Step 1: compared with the full pullback-comparison and adjunction-mate statements and the blueprint's first display; PASS, no change.
- Step 2: compared with naturality of the pullback isomorphism and the mate bijection, and Stacks 0B65's Hom argument; PASS after writing the naturality equality and its transpose explicitly.
- Step 3: compared with global comparison, continuity, etale restriction-injectives, direct-image evaluation, exact inverse image and injective-preservation statements, plus the blueprint's three-term display; PASS after displaying that calculation, checking qcqs/affine transitions and cofinal-tail descent, and justifying the affine-open reduction. The module extension of abelian exactness uses the underlying kernels and cokernels, not an unprovided module-exactness claim.
- Step 4: compared with global comparison on U_W, pro-etale restriction-injectives for both weakly etale maps, exact pro-etale inverse image, the right-adjoint injective-preservation leaf and the operations' section formula; PASS after specifying both restriction maps and the common section complex. Neither U_i nor U_W is asserted affine.
- Step 5: compared with injective acyclicity on affine V, the full comparison-section formula, Leray acyclicity clause (3) and the module-diagram Grothendieck statement, derived basis detection, and the defining transpose formula; PASS after specifying the representing map, its value on a stage section as a map of section complexes (without identifying sheaves on different sites), its compatibility with differentials/restrictions, and the correctly ordered normalization.
- New nodes: none; B1–B7 and the duplicate/restatement/Mathlib-leaf tests require no new-node repairs. All non-elementary added ingredients are existing statements, not new aliases for clauses of the item.

Changes and reasons:

- Expanded Step 2's naturality calculation; the previous sentence left the transposition implicit.
- Expanded Steps 3 and 4's local restriction and three-term cohomology calculation; the previous Step 3 mentioned “outer identifications” without displaying any calculation.
- Added existing citations for direct-image evaluation, module injective representatives, etale exactness, and exact-left-adjoint preservation of injectives. The Mathlib leaf `lem-sp-right-adjoint-preserves-injectives` was checked at `Mathlib/CategoryTheory/Preadditive/Injective/Preserves.lean:49`.
- Added `lemma-weil-pbc-leray-acyclicity` clause (3) for the bounded-below evaluation-acyclic complex, and specialized the existing same-unit `lem-weil-pbc-small-module-diagrams-grothendieck` to the one-object category to supply its Grothendieck hypothesis. Checked the former against `derived.tex`, `lemma-leray-acyclicity`, and the latter's self-contained arbitrary-small-site/module-diagram statement (Stacks 05AB, 079A, 079Q setting). The singleton-diagram equivalence is explicit; no new special-case node is needed. The first dry run refused the alternative `src-right-derived-functor-plus-acyclic-unit` citation on unit-route grounds; removed it after finding these existing permitted-route ingredients. No `tool_uses` record was written.
- Replaced Step 5's backwards `≫` equation by ordinary right-to-left composition matching the statement. Expanded the finite-stage section calculation to identify the named mate, rather than merely its objects.
- Rebuilt citations.json from the full current statements, including hypotheses and conclusions. The previous quotes for `prop-weil-pbc-proetale-constant-exact` were stale and not verbatim; all citations now agree with the repaired steps.
- Independently ran LeanFinder on acyclic derived comparison, grep on `conjugateEquiv|mateEquiv`, and Loogle on `CategoryTheory.Adjunction.homEquiv`; the actual output is in searches.jsonl. Generic mate and derived-factorization declarations do not state the geometric invertibility theorem.

Edge cases: for u an identity, the pullback/counit identities give b the identity; for K=0, all section complexes and all displayed maps are zero-object isomorphisms; for empty U or V, the same calculations give zero complexes and the empty cover detects zero sheaves; for a field base no finiteness or properness is introduced. The equations apply in n=0, n=1 and every integer degree, with no positive-degree-only inference of invertibility. No disputed statement was found. Read the master source only as reference, never as a finished proof. No Lean, compiler, live-project edit, or direct git command was used.

Validation: repaired dry run printed `OK (not pushed)` at b02825289a; preflight passed with zero new nodes.
