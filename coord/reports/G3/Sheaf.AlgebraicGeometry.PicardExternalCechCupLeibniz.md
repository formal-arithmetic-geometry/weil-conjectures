## What changed

Repaired the archived H3 delivery substantively. In
`Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz`, replaced the proof through
an unproved new coordinate lemma with a complete proof from the existing
`picardExternalCechCupDegreeMaps_comm_ι` theorem. Prescribed Cech coordinates identify
chosen bidegree maps with h, h₁ and h₂ on pure tensors. The tensor-total differential
formulas give the two terms, their signs, and the exact degree transports.

In `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate`, closed
its sorry by evaluating the Leibniz equality. Its proof import now points to the
Leibniz module. Both archived signatures and public visibility are preserved.
There are no definitions, instances or target-signature changes. Both files compile
in import order within the single-file limit. Declaration probes in the delivery dry
run execute for both modules; no forbidden axiom or hidden sorry was reported.

## Proved and sorry left

Completed `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz`.
Closed the archived hole
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz_coordinate`
(node `lem-sc-picard-external-cech-cup-leibniz-coordinate`). No textual sorry remains
in either delivered module; no holes are added or split off.

This is a proof from an existing stated dependency, as required by stage 3, not a
claim of axiom-free completion of the dependency closure:
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι` is still
sorry in its existing module and is not changed here. Its node is
`lem-sc-picard-external-cech-cup-differential-coordinate`.

## No longer needed

Removed the private import of
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate` from the
Leibniz module. The coordinate node is no longer a proof dependency of the Leibniz
node; it is retained with its unchanged signature and now a proved evaluation lemma.
No new coordinate face-calculation work is needed. No existing unit step is bypassed:
the route uses the already planned external cup inclusion differential calculation
in unit `sk-prop-av-cube`.

## Where the brief, the DAG or earlier work was wrong

Return point 1 (coordinate probe): the unrelated two-Paper-module import collision
still reproduces in `scratchpad/BatchCollision.lean` without either delivered module.
The current `tools/build.py` batch_checks already retries each unprobed module alone
when the combined probe fails. The delivery tool runs each declaration probe alone.
No project tool or Paper module is edited. The coordinate module now has a complete
proof, not the archived sorry.

Return point 2 (coordinate importer): preserved the exact archived coordinate
signature and visibility. Changed the Leibniz proof to remove its dependency on that
coordinate module. Both modules compile in their new dependency order. There are no
repository importers of either withdrawn module at the current base, so no existing
importer adaptation is required.

Return point 3 (Leibniz probe): the Leibniz module compiles alone and with the coordinate
module. Its new proof uses the existing inclusion-level theorem and contains no sorry.
The historical combined probe collision is handled by the current individual retry;
it does not arise in the delivered module's import closure.

Return point 4 (Leibniz self-importer attribution): no self-import exists. The Leibniz
module imports the differential-coordinate module; the retained coordinate module
imports Leibniz. Their signatures are unchanged and the delivered set compiles.
No forced adaptation of an unheld existing module is made.

The earlier worker missed the existing inclusion theorem as a route and treated the
independent batch-probe collision as an obstacle to any mathematical repair. This
repair closes the extra coordinate hole instead of re-pushing the archived reduction.

## New nodes

`lem-sc-picard-external-cech-cup-leibniz` records the unchanged Leibniz signature and
the route through the existing bidegree existence and differential-coordinate nodes.
The historical module and its node are absent at the current base, so this delivery
restores a full node record. Its declaration contains no sorry.

`lem-sc-picard-external-cech-cup-leibniz-coordinate` restores the archived signature
with a proved coordinate evaluation lemma. Its proof dependency is now the Leibniz
node, preventing a cycle. No new mathematical assumption is introduced.

Change record: `coord/changes/picard-external-cech-cup-leibniz-coordinate.md`.

## Second reading by G3

1. **Statements and accidental changes: PASS.** Both modules and their nodes are
absent from the current repository base; `diff` reports the missing base paths.
I therefore extracted the two archived sources from the repair request's original
delivery diff, compared them with the delivered files, and checked that both theorem
signatures are byte-for-byte identical. The differences are proofs, proof imports,
headers and the coordinate proof docstring. No definition, instance, public visibility,
section variable or target changes. No repository importer uses either absent module.

2. **Proof validity: PASS with open upstream dependencies.** `lcompile.py --all`
compiled Leibniz in 5.1 seconds and the coordinate module in 2.5 seconds, without
warnings. Both contain no textual sorry or forbidden declaration. Scratch-copy
`#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound` and
`sorryAx`; the delivery's individual probes also ran without a forbidden axiom or
hidden local sorry. The inclusion-level theorem remains an existing upstream hole.
The local family choice is inside a theorem proof, from the proved bidegree existence
result; coordinate injectivity determines each chosen pure-tensor value, and tensor
extensionality determines the linear map. No arbitrary witness data is defined.

3. **Split statements and edge cases: PASS.** No new hole is split off. The restored
coordinate theorem is proved by evaluation of the main identity. At p=q=0 the total
sign is +1 and the transported degrees both equal 1; in characteristic two the
integer sign acts correctly. Empty index families make coordinates vacuous, and zero
inputs give zero by linearity. All arguments remain uniform in these cases. I searched
with `msearch.py grep` for cup/Leibniz and total differential variants, and with `rg`
for the same-scheme Cech Leibniz and module AW theorems. Those have different coefficient
models or need additional pullback identifications; no shorter direct theorem for
these prescribed external maps was found. The archived coordinate hole is closed.

4. **Top-down proof and pruning: PASS.** I traced the chosen family, coordinate
uniqueness, inclusion equation, two total differential summands, evaluation on a pure
tensor, and replacement by h, h₁ and h₂. The first sign is 1 and the second is (-1)^p;
the two degree transports match the unchanged conclusion. The archived coordinate
node is the only removed Leibniz proof dependency and is listed under No longer
needed. Both public bidegree imports are needed by the signatures; both additional
imports are proof-only. `sk-prop-av-cube.realized` currently has empty statement and
step lists; this delivery changes none of them and bypasses no recorded unit step.
The main declaration's preserved archived docstring describes the underlying face
argument, rather than the new tensor-total reduction; the report and node explicitly
record the actual new route.

5. **DAG agreement: PASS.** Leibniz uses the existing bidegree existence and
inclusion differential nodes; the coordinate node uses Leibniz. Their proof-dependency
unions, proof steps, origin, source, unit, creation metadata and Lean records agree
with the actual declarations. The coordinate node's old dependency on bidegree is
now replaced by Leibniz; the former is still needed in its signature and public import,
so it is not a prunable module. There is no import or proof-dependency cycle.

Second reading changed only the report: added this five-point review, precise archived
comparison, edge-case and search findings, and the explicit axiom-check limitation.
No Lean proof repair was needed. The final dry run and delivery run perform all
required preflight and individual declaration probes.
