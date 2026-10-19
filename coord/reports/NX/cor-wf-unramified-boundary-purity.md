# Worker report: cor-wf-unramified-boundary-purity

Group NX; stage 1; 2026-10-18. Direct delivery with self-review, as authorized in the dispatcher brief. No other agent was started, and no Lean or compiler tool was run.

## Files written

- `dag/nodes/sec-purity-real-sheaves/cor-wf-unramified-boundary-purity.json`: existing statement node, marked `split`; added the missing curve, boundary, and weight statement dependencies; expanded both imported proof paragraphs; no new node and no Mathlib leaf.
- `citations.json`: eight entries, one for each node citation in the two proof steps, with verbatim statement excerpts.
- `report.md`: this report.

No Mathlib searches were run because this is a project-specific Weil-sheaf corollary, not a candidate Mathlib node, and no new node was created. The search log therefore contains no fabricated Mathlib results.

## Attachments

None. I read the exact blueprint-tagged declarations in the read-only slopmaster2 source: `AlgebraicGeometry.BoundaryDatum.frobeniusWeight_eq_of_isPunctuallyPure` in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Semicontinuity.lean` and `AlgebraicGeometry.BoundaryDatum.isPunctuallyPure_of_isPunctuallyPure_restrict` in `.../Purity.lean`. They are formal representation-level analogues, and both require the additional hypothesis `hD : D.HasMiddleExtensionEulerProduct l ι` together with `BoundaryDatum`/representation data. That hypothesis and data are absent from this item's natural-language statement, so neither declaration states the item exactly under its hypotheses. The second declaration covers only the consequence clause; it does not supply the first clause as a statement of this item.

## WANTED

None. The current main blueprint, the master blueprint, the relevant DAG nodes, and the source modules are present locally.

## What was wrong and what was repaired

The imported node had an empty `stmt_deps` list even though its statement uses the curve setup, local boundary/inertia setup, and both punctual/module weight definitions. These are now recorded as `d-real-setup`, `d-real-boundary`, `def-weil-punctual-weights`, and `def-weil-frobenius-module-weights`.

The imported proof cited the boundary-stalk, semicontinuity, punctual-weight, module-weight, and middle-extension nodes but left the dual-eigenvalue calculation and the finite boundary reduction implicit. Step 1 now spells out the inertia-invariant identification, the dual reciprocal eigenvalues, and the two inequalities yielding equality. Step 2 cites the existing generic `lem-sc-dense-open-finite-complement` tool after geometric base change, and states the direct-image stalk locality used when the other boundary points are removed. The generic tool is declared in `split_report.tool_uses`; no off-unit node was copied or recreated.

The statement itself was retained verbatim. No statement dispute was found. The blueprint proof in `literature/blueprint/main-20261015/.../cor-wf-unramified-boundary-purity.proof.md` agrees with the master proof and is realized by the two steps here.

## What could not be finished

Nothing in the one-level split. The required server preflight and delivery remain to be run by `deliver.py`.

## Not duplicates

No new node is delivered. The finite-complement fact is cited from existing `lem-sc-dense-open-finite-complement`; no duplicate was created.

## Review by NX

I read `dag/nodes/sec-purity-real-sheaves/cor-wf-unramified-boundary-purity.json`, the unit `dag/units/sk-p-real-semi.json`, the chapter record, and both the current main and master blueprint proof files. I also read the complete statements of every cited node. Step 1 uses `lem-wf-boundary-stalk-invariants` for the Frobenius-equivariant inertia-invariant stalk formula, and trivial inertia reduces invariants to the full representation. It uses `lem-wf-boundary-semicontinuity` with beta equal to `w` for the original sheaf and beta equal to `-w` for the dual. The exact weight meanings come from `def-weil-punctual-weights` and `def-weil-frobenius-module-weights`; the reciprocal-eigenvalue and dual-stalk identifications are the elementary finite-dimensional dual calculation written directly in the step. I checked that the second inequality is equivalent to the lower bound on the original eigenvalue and hence gives equality.

Step 2 uses `d-real-setup` for the smooth geometrically connected finite-type curve conventions, `lem-sc-dense-open-finite-complement` for finiteness after passing to the algebraic closure, and `lem-a1-lisse-middle-extension` for the adjunction-unit isomorphism. The finite-complement node states the needed finiteness for a dense open curve; the passage from the geometric base change back to the finite-field curve is only finiteness descent. Removing the other finitely many boundary points leaves the ordinary direct-image stalk at the selected geometric point unchanged by the section formula. Because the sheaf is lisse on all of `C_0`, the local inertia acts trivially, so Step 1 applies; the middle-extension unit then identifies the resulting Frobenius modules. The final conclusion is exactly punctual purity by `def-weil-punctual-weights`.

I checked the edge cases of an empty boundary (the consequence is immediate), the identity open immersion, rank-zero sheaves where the purity assertion is vacuous, and a one-point boundary. Every citation quote in `citations.json` was checked as a verbatim substring of its node statement. No proof step exceeds 2000 characters, there is no new node to search for duplicates or Mathlib matches, and no cycle is introduced. No SGA source was used.
