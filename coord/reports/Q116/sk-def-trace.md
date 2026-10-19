# Worker report: sk-def-trace

## Files written

- `dag/nodes/sec-fourier-transform/sk-def-trace.json`: item, definition-only split; no new nodes or Mathlib leaves.
- `dag/units/sk-def-trace.json`: filled `realized.statement` with `sk-def-trace` and `realized_by` for this key unit item.
- `citations.json`: empty, because the item is a proof-free definition with no numbered proof steps.

## Attachments

None. `FiniteField.fourierTransform` (WeilConjectures/FourierTransform/Classical.lean:50–56) supplies the generic finite-field specialization of the classical sum, but does not state the combined item. `AlgebraicGeometry.WeilComplex.traceFunction` (WeilConjectures/WeilSheaf/Stalk.lean:513–526) supplies a bounded `PadicAlgCl` trace definition, while the item is the broader sketch definition and also contains the classical transform clause. The missing `AlgebraicGeometry.LAdicWeilSheaf.traceFunction` named by the blueprint is not present.

## WANTED

None.

## Corrections and unresolved work

The imported item was `status: imported` with empty dependencies beyond the two blueprint setting nodes. I marked it `split`, reused the existing `def-fd-trace-function` node for the trace-function clause, and retained `sk-def-char` and `sk-def-fourier-set` for the character and finite-field/coefficient conventions. No statement clause or hypothesis was changed, and no new node was created because the only additional clauses are already definitions in the item itself or existing DAG definitions. The item’s `blueprint.same_as` is `[]`; blueprint searches found only this item and its narrower `def-fd-trace-function` child, not another full equivalent.

No proof remains to finish. The source declaration audit is correctly recorded as `closed_part`: the two existing declarations above cover partial pieces, not the exact combined sketch declaration.

## Review by Q116

I read the current `main-20261015` blueprint section `literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/_section.md`, its child `def-fd-trace-function.md`, the chapter record, and the unit record. I also opened the full statements of `def-fd-trace-function`, `sk-def-char`, and `sk-def-fourier-set` in the DAG. The first states exactly the alternating local-Frobenius trace formula for a Weil complex; the second defines the additive character and its extension to `\psi_n`; the third fixes the finite-field and coefficient setting. Those are precisely the notions used by the item’s statement, so they are its statement dependencies.

The item has no proof steps, hence no step citations to quote. I checked that the statement keeps the source’s separated finite-type scheme, `\mathbf F_{q^n}` point, local Frobenius trace, alternating cohomology sum, and classical Fourier sum. I checked edge cases conceptually: for `n=1` the local operator is the first Frobenius iterate, for the zero complex every trace is zero, and for an empty scheme the pointwise definition is vacuous. The generic `FiniteField.fourierTransform` declaration was read directly and rejected as only a specialization; the `WeilComplex.traceFunction` declaration was read directly and rejected as only the bounded adic trace piece. Thus no exact attachment is claimed.

I checked sections B–E of `coord/delivery-errors.md`: the definition remains proof-free, every statement notion has an existing dependency, no duplicate child node was introduced, and no hypothesis was added or dropped. The unit’s realized fields now identify this item, and the item’s blueprint metadata and split report identify the main-20261015 definition. Server checks completed before writing this report: `check_dag OK` and `review_split` reported `sk-def-trace: PASS; 0 new nodes; realizes unit sk-def-trace`.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs to list.

## What could not be finished

Nothing.
