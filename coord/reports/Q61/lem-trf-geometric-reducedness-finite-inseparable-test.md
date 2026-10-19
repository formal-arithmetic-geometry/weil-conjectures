# Q61: lem-trf-geometric-reducedness-finite-inseparable-test

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-finite-inseparable-test.json`: statement, now split in five steps; not a Mathlib leaf. Statement and statement dependencies preserved. No new nodes and no new Mathlib leaves.
- `citations.json`: nine verbatim statement quotations, covering every citation in the five proof steps.
- `report.md`: this report. `searches.jsonl` is the actual log produced by the required search command.

## Attachments

None. Searched the read-only slopmaster2 and upstream master `WeilConjectures/` trees for the exact blueprint id, geometric reducedness, `IsGeometricallyReduced`, finite inseparability, and separably generated reduced tensors. No declaration states the item. Read `WeilConjectures/Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`: its tensor-product theorems require a perfect base field, or extra formal-unramifiedness and finite-type hypotheses; none is an attachment of the finite purely inseparable test. The node has no recorded Lean audit, and no finished declaration was inferred from upstream master.

## Wanted literature

None. All sources used are already present.

## Problems found and changes made

There was no previous sandbox node or report: only brief marker files. Copied the current shared node, which is unsplit and was created by Q66 for the local geometric-reducedness base-change argument. It already records Mathlib searches; retained all of those. Added the five genuine Q61 searches from the new local log, with their actual results. The item is exactly Algebra 030V, equivalence (1) and (5), after swapping tensor factors and expanding geometric reducedness. No statement dispute or source error was found. No hypotheses were added or removed.

Wrote out the proof rather than introducing a new node restating the test. The only substantive inputs are existing nodes for 04KM (making a finitely generated extension separably generated after finite purely inseparable extensions), 030U (reducedness after separably generated extension), tensor cancellation, and flatness of a module over a field. In particular, no use is made of the unsupported inference that Mathlib's algebraic-closure definition already gives reducedness after arbitrary extension. The finite-expression reduction uses an explicit injection, so there is no hidden filtered-colimit claim.

The generic tool uses of `lem-weil-pbc-make-separably-generated` and `lem-weil-pbc-separably-generated-tensor-reduced` are declared in `split_report.tool_uses`. Both are filed in `sk-thm-p1`, but are used solely as the commutative-algebra tools explicitly invoked by the Stacks proof, not as replacement geometry for `sk-i-curve-zero`. The remaining cited statement nodes are Mathlib leaves; the flat definition itself includes precisely preservation of injections by tensoring.

## Not duplicates

No new nodes were created. Searched the whole DAG for 030V, the geometric-reducedness and finite-inseparability concepts, and the labels of 04KM/030U; read the existing helper nodes rather than duplicating them. Ran `tools/blueprint_refs.py ancestor` and searches for `030V`, `geometric reducedness finite inseparable`, and `reduced`. No imported blueprint node states this test. The perfect-field finite-type scheme result `lem-kun-geometric-reduced-perfect` is a different, more restricted theorem; it cannot supply this arbitrary-field, arbitrary-algebra test. The item's ancestry and exact `from.place` are retained, and `same_as=[]` is confirmed.

## Review by Q61

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three-level and tool-use rules in SETUP, the worker role, the stage state, GOAL, the DAG-sync rules, tools README, the whole delivery-errors sections B through E, and the chapter and correct unit records (`sec-trace-formula`, `sk-i-curve-zero`). I also read the parent local geometric-reducedness argument to check why this test is needed. The unit's realization fields are not this item's responsibility and are untouched.

For the item I read `literature/stacks-project/algebra.tex`, definition `definition-geometrically-reduced` and the entire statement and proof of `lemma-geometrically-reduced-finite-purely-inseparable-extension`, verified as Tag 030V in `tags/tags`. The first nontrivial implication there reduces the extension field to finite generation, applies the 04KM square and then 030U, and descends reducedness. The five steps follow exactly that route. I read the source statements of 04KM (`lemma-make-separably-generated`) and 030U (`lemma-separable-extension-preserves-reducedness`), including the latter's distinction between separable and separably generated. There are no new nodes needing separate source audits.

- Step 1 uses the statement of `def-weil-pbc-finite-purely-inseparable-extension`: the identity extension really is included (dimension one, and exponent zero suffices in positive characteristic). Restricting the universal field-extension assertion is elementary. The tensor identity with k uses its usual multiplication and unit.
- Step 2 uses `lem-weil-pbc-make-separably-generated`, whose statement explicitly gives a commutative square, both finite purely inseparable extensions, and a separably generated upper extension. Its finite-generation hypothesis holds because F is introduced as a field generated by a finite list. The E/k edge therefore meets precisely hypothesis (1) of this item. I did not substitute the weaker algebraic-separability API.
- Step 3 uses `lem-weil-pbc-separably-generated-tensor-reduced`, whose statement applies to an arbitrary reduced commutative E-algebra and a separably generated field extension. Here that algebra is D=E tensor_k C, reduced by (1) and factor-swap, and the extension is F'/E from Step 2. The statement of `lem-weil-pbc-tensor-cancel-base-change` gives exactly the displayed forward and inverse maps upon setting R=k, S=E, A=F', B=C. Its scalar structures agree by the commutative square. No finite type, nonzero, or Noetherian hypothesis on C is used.
- Step 4 uses `lem-weil-pbc-module-over-field-flat`, which states that every k-module is flat, together with `def-weil-pbc-flat-ring-map`, which explicitly defines flatness by preservation of injections. Therefore tensoring the injective field map F to F' with C is injective. The nilpotent calculation then proves reducedness of the source in three lines. This does not invoke an unstated theorem on descent, or rely on the proof of a cited node.
- Step 5 uses `def-weil-pbc-module-tensor-product`, whose statement says pure tensors generate the module, giving the finite sum. The same two flatness nodes make tensoring F into K injective. The finite coefficients define a finitely generated subfield F, so Step 4 applies; injectivity first reflects z_F^n=0 and then z_F=0 gives z=0. This expands the finite-generation reduction in 030V/00I3 directly and requires no new lemma or colimit theorem.

I opened the statement of every cited node; `citations.json` copies those statements verbatim without changing a quotation to fit a use. I checked C1 and C4 separately: the only non-elementary scalar-extension inputs have nodes, and each cited statement gives exactly the needed hypotheses and conclusion. Factor-swap and the tensor unit are elementary ring identities; tensor cancellation is nevertheless cited rather than concealed. Each proof step is under 750 characters, so none triggers the 2000-character long-step check or conceals an additional comparison lemma.

For B and D I checked that no new node is elementary, a duplicate, or a restated clause: there are no new nodes at all. The proof carries the argument itself and proof_deps is exactly the union of uses. No citation points back through this item: the three field-theory/tensor inputs are existing generic helpers with earlier proper-base-change ancestry. The server dry run will check the full graph as well.

For E I tested the zero algebra (all tensors zero, flatness still applies), C=k, the identity extension F=k, and arbitrary non-finitely-generated C and K. In characteristic zero the purely inseparable square has trivial purely inseparable edges, and 04KM still applies. In characteristic p the finite extension E/k in the square is exactly among the tested extensions. For a failure example, k=F_p(t), C=k[u]/(u^p-t) is reduced but not geometrically reduced: over E=k(t^(1/p)) the nonzero element u-t^(1/p) has p-th power zero. Thus merely reduced C would not suffice; this split retains the finite purely inseparable tests. For C=k[epsilon]/(epsilon^2), the E=k test already fails, as required. No place uses an unstated perfection, finite-generation, or nonzero hypothesis.

Mathlib searches used only `msearch.py`: LeanSearch, LeanFinder twice with different phrasings, Loogle, and the required grep. Read every returned hit group and the pinned `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean` (especially its TODO and scalar-extension instance), plus `Mathlib/RingTheory/Unramified/Field.lean` for the extra hypotheses of the other candidate. Loogle's joint pattern returned no hits. Semantic results included the algebraic-closure test and finite-subalgebra criterion, neither the finite purely inseparable criterion nor an arbitrary-field-extension theorem. No service was reported unavailable. No searches were invented. No SGA source, Lean writing, compiler, Lake, or local DAG/preflight checker was used.

## What remains unfinished

Nothing in this one-level split. The already-existing helper nodes retain their own proof obligations. Required server dry run and push are performed after this report is written.

## Validation

The required `deliver.py Q61 lem-trf-geometric-reducedness-finite-inseparable-test --no-push .` exited 0 and printed `OK (not pushed)` at 23b2d3eff2: server preflight passed. No repairs were required. This is direct delivery under the current brief; the legacy brief-marker files do not require a second worker.
