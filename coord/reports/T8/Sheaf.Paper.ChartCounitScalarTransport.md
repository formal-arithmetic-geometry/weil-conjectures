## What changed

Completed `AlgebraicGeometry.ProEtale.ChartFiniteRing.chartCounitScalarTransport_etale`
in `Sheaf.Paper.ChartCounitScalarTransport`. All existing public signatures and the item’s data
constructions are preserved. The already proved pro-etale transport remains intact.

The proof constructs the generator-normalized coefficient line, identifies its ordered
coordinate comparison with the existing raw chart comparison, and applies
`rawChartScalarCounitPasting`. Private proved helpers derive the graph-normalized left
coefficient square directly from the sum/composition squares and rewrite the actual
Datum counit using uniqueness of normalized Tate transport and projective-line data.
A category-theoretic naturality/cancellation calculation combines those equations.
The input compactifications remain arbitrary, as required by the source Charts argument.

Added proof imports for the existing normalization, raw pasting, and uniqueness APIs.
Updated the item's DAG proof and proof dependencies to record this actual assembly.
Repaired the unclaimed `Sheaf.Paper.FiniteSmoothCoefficientArrows.scalarSingleMap`
to use the existing shared adjunction-transpose presentation. Its signature is preserved,
and the proved generic `scalarSingleMap_cochain` equation specializes to the original
formula. This removes costly expansion in the chart coefficient-line normalization. No consumer
source adaptation, new module, or new node is needed. The change record is
`coord/changes/T8-scalar-single-compact-adjunction.md`. The generic original-formula
proof is recorded on the existing coefficient-arrow definition node.

Removed the inherited warning-suppression option in `FiniteSmoothCoefficientArrows`
after the return of head `9b58f0973ea`: the landing scanner treated the dotted option
name as an unattributed hole. The option was unnecessary in this fully proved module.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.ChartFiniteRing.chartCounitScalarTransport_etale`
(`lem-sp-chart-counit-scalar-transport`). There were 1 and there are 0 holes in the
item module. Added 0 holes and split off 0 statements. All private helpers are proved.
The repaired coefficient-arrow module also has zero holes. The theorem uses the existing
declared geometric input theorems;
this is a proof from those library dependencies, not a claim that their holes are closed.

## No longer needed

No original imports were removed. Removed the unused proof import
`Sheaf.Paper.EtaleProEtaleScalarMate` from the item module, and the experimental proof import
`Mathlib.Logic.Small.Defs`. The experimental proof import of
`Sheaf.Paper.FiniteTateScalarSourceNormalization` is no longer needed after the compact
scalar/single definition repair; the original cochain formula is preserved by a proved
API equation. The proof does not require
`lem-sp-chart-left-scalar-normalization` / `Sheaf.Paper.ChartLeftScalarNormalization`:
its needed coefficient square follows directly from the existing sum and composition
coherence, and its counit comparison is proved from Datum.etaleCounit and uniqueness.
It does not require `lem-sp-left-comparison-scalar-counit-pair` /
`Sheaf.CategoryTheory.LeftComparisonScalarCounitPair`: the needed componentwise
naturality and inverse cancellations are private proved helpers. These two planned
proof dependencies were removed from this item's node; no modules are withdrawn.
The prior pro-etale proof already uses componentwise geometric counit evaluation
rather than the generic site-conjugacy theorem, which remains unnecessary here.

## Where the brief, the DAG or earlier work was wrong

The shared item currently has one remaining sorry, not the two holes mentioned in
its older statement review: M9 has already proved the pro-etale clause. The existing
sandbox candidate was repaired against the current library. The ambient
scalar helper needs explicit inclusion of annihilation hypotheses used only in its proof.
The full candidate exceeded the file limit because the expanded scalar/single definition
made kernel checking expensive; the equivalent shared transpose and original-formula
equation address that definition issue. Neither repair changes the mathematical statement.

The planned ChartLeftScalarNormalization module is absent in the current library.
The proof uses the existing sum/composition squares directly, preserving the unit's
sum-then-ordered-affine route and all actual counit normalizations. Edge cases are
retained: zero coordinates use identity recursion; N=1, zero rings, empty schemes,
and non-flat coefficient maps introduce no extra hypotheses.

The item and coefficient-arrow repair compile together with zero holes and no warnings.
Because the repaired map appears in target definitions, its original-formula equality
and preservation of target meaning are part of the independent definition review.

The returned line 29 was an option name, not a proof hole. Removing that option
repairs the reported attribution failure without changing any declaration or proof.

Delivery validation also exposed a marginal compile timeout. The normalization field
now supplies `Eq.refl` with its right-hand scalar formula explicitly, avoiding the
conversion term chosen by tactic reflexivity. Profiling verified the complete item
on the project server in 54.7 seconds with this proof term. No signature or map changes.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
