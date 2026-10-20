## What changed

Retire `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing` in favor of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`, the assigned
zero-hole retirement in `coord/retire-items.tsv`. Remove the unused private import
from the current consumers `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange`
and `Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleLocalizationComparison`.
Migrate the newly restored consumer
`Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` to the upstream import; its
existing gluing application and complete proof stay verbatim. Point
`lem-pur-sheaf-hom-cover-gluing` at the proved upstream theorem, retaining its proof
route. Change record: `coord/changes/X5-retire-hom-cover-gluing.md`.

Repair of returned head `6814f6bed`: refresh all consumer files from current
`sheaf-dag` (initial repair snapshot `f5dbb5f7608`). In particular,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` now has a complete
proof and already omits the retired import. Its current version is retained
verbatim and recompiled; this delivery makes no change to that module. The new
finite-etale consumer and subsequently restored self-Tor consumer are migrated in
the same packet.

## Proved and sorry left

The assigned module had zero holes: 0 closed, 0 added, 0 split off. Its proved
`SheafOfModules.existsUnique_hom_of_cover` remains in the upstream module, with
weaker pullback assumptions and the same conclusion. No upstream source changes.

The conormal and finite-etale consumers retain their existing holes unchanged:
`AlgebraicGeometry.ConormalGradedAlgebra.existsUnique_baseChangeMap`
(node `lem-pur-conormal-algebra-flat-base-change`) and
`AlgebraicGeometry.ProEtale.finiteEtale_localizationExtensionIso`
(node `lem-sf-finite-etale-proetale-localization-comparison`). No proof is claimed
for either. The current `SheafOfModules.finite_free_dual_pullback` and
`AlgebraicGeometry.selfTor_conormal_dual_chart_iso` proofs are preserved.

## No longer needed

Pruned module: `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
Remove its two remaining private import references from the conormal and
finite-etale consumers. Neither of those proof bodies uses the theorem, so neither
needs a
replacement import. The self-Tor consumer uses the theorem and now privately
imports its upstream module; the application needs no binder adaptation. The
finite-free-dual consumer already has no such import.
The gluing node remains needed and points to the upstream theorem. No blueprint
unit, proof step, or upstream declaration is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

This is the queue's zero-hole retirement assignment, rather than a new proof task.
The old kept-copies table records a different upstream API: the twin requires
pullbacks between covering arrows, while the former local theorem required all
pullbacks against covering arrows. The local hypothesis supplies the upstream
instances, and the conclusion agrees.

The previous delivery predated the completed finite-free-dual proof and the new
finite-etale consumer. The self-Tor consumer was restored during the submission
checks, requiring an additional import migration. Reusing an old consumer snapshot
would overwrite current work.
This repair preserves current source, removes the two unused imports, and migrates
the self-Tor import.

## Forced adaptations

The conormal and finite-etale modules are currently unclaimed. Each changes only
by removing the private import of the withdrawn module; all signatures, visibility,
definitions,
proof bodies, and public imports remain identical. The retirement assignment
requires these references to disappear. No compiler failure or theorem adaptation
is claimed. The original three checked consumer versions were compiled with `lcompile.py`;
the unchanged finite-free-dual file was checked for verification and its overlay
was then removed from the sandbox to avoid carrying stale source.

`Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` (holder A9) changes only
its private gluing import to the upstream twin. The original imports the explicitly
withdrawn module, so this migration is required even if the published baseline
still supplies that module. No declaration, proof body, or public import changes.
The updated consumer is compiled with `lcompile.py`.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
