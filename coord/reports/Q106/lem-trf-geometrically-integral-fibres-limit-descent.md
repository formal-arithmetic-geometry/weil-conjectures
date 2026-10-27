# Stage-1 delivery: lem-trf-geometrically-integral-fibres-limit-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-integral-fibres-limit-descent.json`: statement, split, no Mathlib match; six proof steps using existing nodes.
- `citations.json`: all 20 step/node pairs, quoting their full statements verbatim so their hypotheses remain visible.
- `report.md`: this report. `searches.jsonl` is the search tool's log.

New nodes: 0. New Mathlib leaves: 0. The item statement and statement dependencies are unchanged. Existing source, creation and blueprint provenance and earlier searches were preserved; six actually executed Q106 searches were appended.

## Attachments

None. Searched the whole project `lean/WeilConjectures/` for the exact blueprint id and the notions geometric integrality, descent and limits. The existing field-extension descent results and proper/smooth descent results do not state the eventual directed-base-ring assertion. The reduced-fibre limit theorem in `lean/Sheaf/TraceFormula/GeometricallyReducedFibresLimitDescent.lean` has `sorry` and covers only reducedness, so is not an attachment.

## WANTED

None. All mathematical sources needed are present locally.

## Corrections and route

No statement dispute or mathematical correction was needed. The unsplit item already names the simultaneous constructible-locus argument of Stacks 05FG and 05FH. Their literal statements select Noetherian models, while their proofs use exactly the constructible-image reflection mechanism applicable to this fixed model over an arbitrary directed system. I supplied that argument with every input cited, without adding a flatness, injectivity or Noetherian hypothesis.

I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof. This item is an existing lower-level algebraic approximation input on the inherited semistable-alteration/flattening branch, not the unit's key statement. No unit or chapter record was changed. The exact inherited `blueprint.from.place` and via chain are retained. Whole-blueprint searches for `geometrically integral`, `geometrically irreducible`, `integral fibres`, `integral fibers` and `limit contained` found no node stating this item. No SGA source is used.

The sole off-unit, non-Mathlib, non-closed generic tool is `lem-sbc-subset-geometric-irreducibility`. Its explicit `split_report.tool_uses` entry explains its use to test whole-fibre geometric irreducibility on a separably closed extension. This does not replace a unit proof step. All other off-unit inputs are definitions, Mathlib leaves, or the Lean-closed limit-image reflection theorem.

## Not duplicates

No new node is proposed. Existing reduced-locus, irreducible-locus, component-count comparison, spectrum-colimit, affine qcqs, tensor pushout, affine fibre-product and constructible-image reflection nodes are reused. In particular I did not turn geometric irreducibility of one fibre, the one-component criterion, the intersection of two constructible subsets, or one of the item's own clauses into a new node.

## Mathlib searches

I ran the required wrapper for LeanFinder, Loogle, grep and LeanSearch, then used a second natural-language phrasing and a second grep pattern. All six calls succeeded; exact query texts and digests are in the item and `searches.jsonl`. I read the returned signatures and `Mathlib/AlgebraicGeometry/Geometrically/Integral.lean`, notably its geometric reduced/irreducible decomposition and base-change instances at lines 40–70. These describe geometric integrality and preservation under base change, not reflection to a finite stage of a directed ring diagram. The other hits give essential-finite-type factorization, integral morphisms, or geometric reducedness over a fixed field, not this assertion. No unavailable service was recorded as an absence.

## Review by Q106

I checked the split against delivery-errors B–E with the cited node statements open. There are no new statements to audit for missing objects, duplicated clauses or unjustified hypotheses. The item introduces its small nonempty directed system, compatible unital maps, fixed finitely presented algebra, all base-changed algebras and residue-field fibres. Its geometric integrality convention includes nonemptiness. All six steps are below 1000 characters, so none passes the 2000-character long-step threshold or hides a long standard comparison.

For the item source I read `more-morphisms.tex` proofs of 05FG (`lemma-Noetherian-approximation-geometrically-reduced`) and 05FH (`lemma-Noetherian-approximation-geometrically-irreducible`), including their constructible loci and common refinement. I also read 0579 (`lemma-geometrically-reduced-constructible`), 055B (`lemma-nr-geom-irreducible-components-constructible`), 0576, 0555 and 0556 in that file, `limits.tex` 01YW and 05F4, `schemes.tex` 01I4, `topology.tex` 004W, and `varieties.tex` 054P and the following separably-closed irreducibility lemma. These sources support all parts of the existing input statements actually used.

1. Step 1 cites `lem-weil-pbc-spec-colimit-limit`, which explicitly provides both the scheme limit and affine transition maps for this ring colimit. `lem-weil-pbc-affine-scheme-qcqs` supplies both compactness conditions for every spectrum, without assuming the rings Noetherian. `lem-weil-pbc-fibre-product-affine-spectra` identifies each tensor algebra's spectrum with the specified pullback, including its projection maps. I checked these are the actual scalar extensions in the item's statement, rather than an unrelated chosen approximation.
2. Step 2 uses `lem-trf-geometrically-reduced-fibre-locus` and `lem-trf-geometrically-irreducible-fibre-locus` at the original finitely presented map. Both explicitly allow nonflat maps and arbitrary base rings. The Boolean-algebra assertion is actually part of `def-weil-constructible-subset`, so its citation supports closure under intersection. `def-pc-geometrically-irreducible` defines all four geometric predicates and `def-pc-integral-scheme` includes the reduced/irreducible/nonempty equivalence. These support identification of the intersection with the desired good locus, after every residue-field extension.
3. Step 3 uses the fixed separable closure supplied by `def-pd-separable-closure`, maximality from `def-weil-irreducible-components`, and the explicit covering assertion of `lem-sc-irreducible-components-cover`. Exactly one component therefore equals the whole nonempty fibre, and an irreducible nonempty fibre has just itself as a maximal irreducible subset. `lem-sbc-subset-geometric-irreducibility` applies with the whole subset of the fibre and its separably closed extension; its statement, not its proof, supplies irreducibility and nonemptiness after every other field extension. This is a few-line consequence of the cited statements, so this step is elementary relative to them; no finite-type or component-finiteness assumption is smuggled in.
4. Step 4 uses the arbitrary-base-change equality explicitly stated in `lem-trf-geometrically-reduced-fibre-locus`. For irreducibility, `lem-trf-geometric-fibre-component-count-base-change` explicitly supplies equality of geometric component counts for every scheme base change; step 3 converts its count-one assertion into geometric irreducibility in both directions. This avoids incorrectly taking an unstated base-change theorem from the irreducible-locus node, whose statement only gives constructibility. The affine fibre-product and tensor pushout statements support the displayed fibre algebra comparison; both maps are written on pure tensors and are inverse there. No flatness or injectivity of the ring map is used. In particular geometric irreducibility is reflected, not merely preserved.
5. Step 5 applies `lem-weil-pbc-limit-contained-in-constructible` only after verifying every stated hypothesis: a directed system of qcqs schemes, affine transitions, its actual scheme limit, a constructible subset at the fixed index, and image containment at that index. Step 4 and the hypothesis give the last condition without asserting that the limit maps surjectively to any stage. The cited statement already gives all sufficiently late indices, so the same b works on the whole tail, not merely one selected stage.
6. Step 6 uses the base-change comparison already proved in step 4 and only the two geometric/integral definitions. Each extended fibre is reduced, irreducible and nonempty; it is therefore integral. The two universal quantifiers over indices and primes follow directly from step 5 and the locus equality. There is no dropped conclusion or hypothesis.

Edge checks: if A is the zero ring, its spectrum is empty and the hypothesis is vacuous; the limit-contained-in-constructible lemma still applies and forces the necessary eventual containment, even if E is empty. Concretely 1=0 in a directed ring colimit is witnessed at a stage. If C_a is zero and A is nonzero, empty fibres cannot satisfy geometric integrality (their component count is 0, not 1); no false nonemptiness follows from geometric reducedness. Polynomial algebras and the constant diagram give the expected assertion with b=a. Noninjective quotient maps cause no problem since both fibre comparisons are valid for arbitrary unital base change. Inseparable residue-field extensions are included by the geometric component-count statement and the separably-closed test. Reducible but reduced fibres are excluded by the count-one condition. No Noetherian, flatness or surjectivity condition enters the argument.

I checked that citations.json includes every step/use pair and that every quote is verbatim from the corresponding live node statement. I kept the elementary component/intersection/tensor consequences inside the proof instead of creating redundant nodes, and introduced no circular dependence on the item or one of its clauses.

## Unfinished work

None in the requested stage-1 split. No Lean was written and no compiler, Lake or build tool was invoked. The required server dry run and direct delivery follow this report.
