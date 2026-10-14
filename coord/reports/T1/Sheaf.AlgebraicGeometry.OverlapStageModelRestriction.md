## What changed
Replaced the first worker's `Core` restatement with an actual reduction of
`overlap_stage_model_restriction`. Its statement, visibility and docstring are
unchanged. The proof substitutes the four canonical comparisons, applies a
proved pair base-change formula, factors the two chart comparisons, and uses
tensor compatibility and naturality to identify the middle morphism.

Added `OverlapBaseChangeFormula` (proved from the existing upstream `pullHom`
component formula) and `OverlapModelChartFactorization` (one chart isomorphism
identity, still open). Both are new modules with matching nodes. Their imports
are public only where their signatures require them; the item's two new imports
and the formula's upstream `AffineDescent` import are proof-only.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.overlap_stage_model_restriction`.
Also proved the new helper `AlgebraicGeometry.overlap_base_change_formula`.
Added exactly one hole:
`AlgebraicGeometry.overlap_model_chart_factorization`, node
`lem-pc-overlap-model-chart-factorization`. This is the only delivered `sorry`.
It has no transition morphisms, compatibility equation or pair transport
conclusion: it is the single-chart exterior comparison identity, used twice.
One original hole closed and one simpler hole added is a decomposition, with
net zero holes closed, not a complete proof of the import closure.

## No longer needed
Removed the never-landed `Sheaf.AlgebraicGeometry.Core` and its restatement node
`lem-pc-overlap-stage-model-restriction-core` from this delivery. They never
belonged to the repository. Removed the first worker's unnecessary change
record: no existing statement, definition or public import changes.

Relative to the repository node, these old proof dependencies are no longer
direct dependencies of the item:
`lem-sc-left-adjoint-composition-iso-associativity` and
`lem-pc-module-pullback-adjunction`. They remain prerequisites of the smaller
chart identity; this is not a claim that their modules leave the target closure.
The other three old dependencies remain recorded. No repository import was
removed and no existing library module is claimed pruned.

The first report's claim to prune `AffineDescent` was not retained: the new
proved formula uses its existing component formula through a proof-only import.
The abandoned chart-coherence module referenced by earlier probes is absent
from this repository and is not imported or recreated under its former name.

## Where the brief, the DAG or earlier work was wrong
The first worker's `overlap_stage_model_restriction_core` was equivalent to the
item after substituting its four named canonicality equations. Applying it
proved nothing and did not meet the strictly-smaller split requirement. Its
node was copied from the item, including unrelated historical review metadata;
its recorded proof was not its Lean proof, and its docstring gave no complete
argument. The original change record did not describe a signature change.

The abandoned expansion supplied an incorrect one-chart equation for chart a:
the chart map's comparison with the original chart projection uses the second
pullback projection, even on chart a. The replacement factorization applications
use that second projection for both charts, and the overlap lift's first or
second projection respectively for a and b.

Elaboration of a fully expected pair-formula type tried to normalize nested
cover and pseudofunctor definitions. Inferring the formula first and explicitly
reducing its let bindings avoids this expensive comparison. Generalizing the explicitly constructed lift together with its equality keeps
its universal-property proofs attached while avoiding repeated unfolding of the
lift during the final comparison. No mathematical definition or existing
statement was changed to obtain this improvement.

## New nodes
`lem-pc-overlap-base-change-formula` records the proved module pullback formula
for pair base change, using the existing upstream component formula.

`lem-pc-overlap-model-chart-factorization` records the remaining single-chart
comparison factorization. Its statement includes the full commuting diagram,
all canonical isomorphisms and the exact equality; its docstring and node give
the adjunction comparison and pentagon proof. Searches with different wording
in LeanFinder, Loogle, Mathlib and the local library found component APIs but no
exact chart factorization. LeanSearch was attempted and returned a service error.

## Second reading by T1
1. Compared all delivered modules to the repository. The only existing module
is the item; its theorem signature, visibility and docstring are byte-for-byte
unchanged. All other delivered declarations are new; no definitions changed.
2. Compiled the delivered modules with `lcompile.py`. Checked for forbidden
constructs and data holes. Verified the source tags: 0095 defines module
pullback, 0096 proves its adjunction, 0097 gives canonical composition, and
01ZR explicitly leaves the Zariski gluing details to be supplied. The pair formula
uses exactly `propext`, `Classical.choice`, and `Quot.sound`; the item and chart
theorem additionally use the expected `sorryAx`. The item and pair formula have real proofs; the only
remaining hole is the explicitly named single-chart theorem. Scratch axiom
checks allow only `propext`, `Classical.choice`, `Quot.sound` and the expected
`sorryAx` from that theorem or already-open prerequisites.
3. Rejected and removed the core restatement. Read the new factorization from
its source comparison calculus and checked identity maps, repeated charts,
zero modules and empty overlaps: cancellation uses isomorphisms only, with no
faithfulness, nonemptiness or finiteness assumption. The theorem concerns just
one chart comparison, not the pair transport assertion. Searched independently
for duplicates and used the existing upstream `pullHom` formula.
4. The proof keeps the canonical restriction/composition route and implements
the pair formula and middle cancellation. New imports used solely in the proof
are plain imports. The unit `sk-thm-picard-semicon` has empty `realized` statement
and step lists in the repository; these were left unchanged. All five old item
proof dependencies are accounted for above: three retained and two moved to
the chart theorem. No existing module is claimed unreachable.
5. Replaced the stale item proof record with its actual three-step reduction.
Both new nodes have self-contained statements, source citations, search records,
creation/blueprint metadata, exact Lean signatures and proof dependencies equal
to their steps' uses. No inherited review metadata is used for new nodes.

Changed in the second reading: removed the invalid restatement and change
record; wrote the actual reduction and proved pair formula; isolated one genuine
single-chart comparison hole; repaired the chart-a projection equation; corrected
the DAG, pruning claims and hole accounting; removed the first worker's
file-level local attributes, which were unnecessary after the lift was kept
explicit and were rejected by the interface guard.

Validation: the three modules compile cleanly; the original theorem signature
and docstring match the repository exactly. Independent axiom probes confirm
the axiom lists stated above.
