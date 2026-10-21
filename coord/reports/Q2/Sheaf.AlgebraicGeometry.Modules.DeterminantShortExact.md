## What changed

Retired Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact, the zero-hole
retirement item listed at coord/retire-items.tsv:1725. Its sole direct consumer,
Sheaf.AlgebraicGeometry.DeterminantDualEvaluation, now privately imports the
complete adopted WeilConjectures twin. Its proof extracts invertibility of the
canonical exteriorPower and transfers it by IsInvertible.of_iso along the
inverse exteriorSheafPowerIso. The consumer's public imports, statement,
visibility and definitions are unchanged. No adopted source file changes.

The item node retains the determinant theorem on the adopted declaration, with
its full verbatim signature and proof dependencies matching the adopted proof.
The consumer node records the comparison used for the transport. The other DAG
parent, lem-sc-riemann-roch, still uses determinant multiplicativity through this
node. The unit route and mathematical statement are preserved.

Change record: coord/changes/Q2-retire-determinant-short-exact.md.

## Proved and sorry left

The assigned item contains zero holes before retirement: proved 0 of 0 sorries,
0 split off, 0 added, 0 remaining in the delivery. The adopted
AlgebraicGeometry.Scheme.Modules.determinant_shortExact is already complete;
AlgebraicGeometry.determinant_dual_evaluation remains fully proved with its
original signature. The retired duplicate and its private
exteriorSheafPowerIso_hom_wedge helper need no separate proof work.

The adapted consumer compiles without warnings. A scratch compile of the
original proof with only its import migrated fails with an exteriorPower versus
exteriorSheaf invertibility type mismatch, confirming the required API change.
An additional single-file check of unchanged ShiftedDeterminantDualEvaluation
hit the 60-second limit both against the adapted consumer and against the
original published baseline. Profiling did not return diagnostics before the
same timeout. This pre-existing transitive compile limitation is reported; no
change to that file is delivered. The direct consumer compiles cleanly. Delivery
also runs the axiom probe and server preflight.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact. Its sole
consumer replaces its private import with the adopted twin.

The item no longer needs Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible
(node lem-sc-exterior-sheaf-top-invertible), or its private comparison transport
from Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
(node lem-sc-exterior-sheaf-power-comparison). The adopted theorem uses the
proved isInvertible_exteriorPower instance and the adopted exteriorTensor_lift_hom_ext
(node lem-sc-exterior-tensor-lift-hom-ext). The comparison is still required by
the consumer and is explicitly added to that node's proof dependencies.

The retired item's public imports of ExteriorSheaf, TensorSection, LocallyFree,
and ShortExact disappear with it. The adapted consumer keeps every existing
public import. The adopted existence dependency
lem-sc-determinant-short-exact-exists is retained. No source-library declaration
or other DAG node is withdrawn; no further module is claimed globally unused.

## Where the brief, the DAG or earlier work was wrong

The generic prove brief describes a holed module, but this assignment is the
listed retirement of an already complete duplicate. The API difference in the
retirement table is real: an import-only migration fails, since exteriorPower M d
and exteriorSheaf M d require the existing comparison isomorphism. Transporting
invertibility fixes it without weakening the consumer or editing upstream.

No false statement, new node, definition repair, or target change was needed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
