# Stage-1 report: lem-per-integral-pullback-bounds

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-integral-pullback-bounds.json`: statement split into five steps; Mathlib verdict no match.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. All needed intermediate results already exist. Auxiliary source extraction and the JSON assembly script are sandbox research files, not delivery node files.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the item tag, integral pullback and completed pullback. The completed-exchange module defines the functor and unit, but does not prove this item's constructible-category, ambient interval and unit clauses together. An ordinary module completion or finite-coefficient pullback theorem does not attach this item.

## Wanted

None.

## Problems corrected

The item was statement-only. Its statement is unchanged. Its stronger completion-unit assertion is not simply Lemma 6.5.9(4)-(5): those clauses give completed pullback and preservation of constructibility, not invertibility of the ordinary pullback's completion unit. Step 1 proves ordinary pullback constructible using existing ordinary stratified-perfect models; only then Step 2 applies the completion-unit criterion. The proof is marked agent assembly, since the exact witness category and normalized comparisons are DAG refinements of the cited paper.

No claim is made that ambient support in [a,b] implies finite reductions have support in [a,b]. For example, a residue module in degree zero can acquire degree -1 under derived residue reduction. Likewise a bounded finite-projective representative need not have terms confined to its cohomological interval. Step 4 uses the existing scalar-model lemma's ambient cohomological implication instead.

## Unfinished work

None for this one-level split. Existing cited nodes retain their own stage statuses; none was rewritten or split here.

## Not duplicates

No new nodes. Whole-DAG concept searches and blueprint searches for completed pullback, completion unit, perfect pullback, scalar perfect and cohomological interval found the existing tools cited in the proof. The item's nearest ancestor is `lem-per-smooth-pullback-t-exact`; the current main-20261015 first proof paragraph is its ordinary cohomology pullback assertion. No blueprint node states the present integral, arbitrary-morphism package exactly.

## Review by Q83

I read Bhatt–Scholze, The pro-etale topology for schemes, Lemma 6.5.9 and its proof, Remark 6.5.10, and Proposition 6.6.11 and its proof, in the provided PDF (printed pages 50–54). The latter uses stratified locally constant perfect values, and the former uses finite reductions and the completion adjunction. I also read the current main-20261015 ancestor proof. Its use of exact cohomological pullback is the portion served here; no Fourier/perverse or smooth-purity route is replaced. There are no new nodes needing separate source verification.

Step 1 uses `lem-weil-pbc-integral-stratified-perfect-characterization` in both directions. Its statement explicitly includes the actual completed ring category, compatible etale origins and uniform reduction bounds. `lem-tw-ordinary-pullback-stratified-models` explicitly concerns ordinary pullback before completion, gives the fibre-product stratification and covering charts, and identifies the output with the same scalar complexes. These are the precise statements needed, rather than proofs hidden below a definition. The schemes in the item satisfy the noetherian and finite-dimensional hypotheses of the characterization and the noetherian hypotheses of the ordinary model lemma. The latter imposes no noetherianity on chart schemes, nor flatness, separatedness or base-field linearity on the morphism. This yields completeness of the ordinary output without assuming the desired completion-unit assertion.

Step 2 reads the last paragraph of `def-weil-pbc-completed-pullback`, which identifies its constructed map as the completion unit. `lem-weil-pbc-constant-completion-equivalence` identifies quotient and Koszul completion including the units, and `lem-weil-pbc-ringed-koszul-completion-reflector` explicitly says its unit is invertible precisely on locally derived complete objects. The hypothesis comes from Step 1. `lem-weil-pbc-uniform-complete-triangulated` includes closure under isomorphism. Thus this proves invertibility of the specified map and membership of its target, not just the existence of an unspecified isomorphism.

Step 3 uses the exact functor and coherent shift statement of `lem-cbc-completed-pullback-triangles`, together with the inherited triangles of `lem-weil-pbc-uniform-complete-triangulated`. Its completeness hypothesis holds for every vertex in the source category. Scalar linearity is the termwise equality on maps in the definition's A-module tower construction. `lemma-weil-pbc-completed-pullback-reduction` states the natural canonical reduction isomorphisms, quotient transitions and normalization cocycles taken here. It does not claim compatible origins: those were obtained separately in Step 1. I did not infer uniform witnesses from unrelated levelwise existence assertions.

Step 4 uses the first and second paragraphs of `lem-a1-integral-stratum-chart-restrictions`: exact restriction of ambient cohomology on source and target, scalar models, and the fibre-product chart comparison. The specified integral and completed functors are identified by the reduction- and shift-compatible `lem-a1-integral-pullback-completed-comparison`. `lem-a1-completed-perfect-scalar-pullback` explicitly includes the final implication preserving any ambient [a,b], and applies to arbitrary chart morphisms; no noetherian hypothesis is imposed on these charts. `lem-weil-pbc-local-derived-restriction-comparisons` compares exact inverse-image/slice restriction with ambient cohomology over the actual inverse-image ring, and `lem-weil-pbc-noetherian-stratum-detection` detects vanishing on the resulting covering family. Every one of these public statements was opened and read, and is quoted verbatim in citations.json. I checked there is no dependency path from any cited tool back to the item.

Step 5 uses precisely the ambient-vanishing description of the halves in `prop-weil-pbc-integral-tstructure` and boundedness in the stratified-perfect characterization. Choosing the other endpoint as min(a,0) or max(b,0) makes the interval argument valid even for zero objects. The ordinary model lemma permits discarding empty strata, and stratum detection also covers an empty family on an empty scheme. The zero perfect model gives zero on every chart. As further small cases I checked the identity morphism, a map between geometric points, and the torsion scalar model [A --varpi--> A], whose nonzero cohomology is a residue module: the cited scalar interval implication preserves its degree, although its chosen terms and its finite reductions occupy more degrees. No flatness of the completed coefficient structure map is used.

For delivery-errors B–E: no new statement-only nodes or TeX/definition issues are introduced; every cited non-elementary fact is in an existing statement (C1/C4), with exact quotes and declared off-unit tool uses. This is an assembly using existing intermediate results, not a relabelled new node or one-clause duplicate. No proof step exceeds 2000 characters. All scalar, scheme and completeness hypotheses have been checked above. No SGA source, Lean writing or compiler command was used. Recorded Mathlib searches were run through msearch.py, with two conceptual phrasings. Their hits concern ordinary finite-module completion, free-sheaf unit pullback, generic truncations, or scheme morphism/site infrastructure; none states this item. I read the ordinary completion and ell-adic site source files to check that distinction.
