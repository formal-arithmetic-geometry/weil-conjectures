# WeilConjectures.complete_residue_cohomology_bounds proof scope

## Reason

The completed proof needs explicit coefficient-sheaf instances and a local
elaboration scope for the derived-category constructions. The delivery checker
requires a change record because these commands occur in an exposed module
section. The target theorem signature and all existing public declarations keep
their statements and visibility. The proof-only imports are narrowed to the
modules actually used. The new filtration declaration is recorded separately by
its DAG node.

## Old

```lean
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

set_option backward.isDefEq.respectTransparency false
```

The original module had no local instance-suppression block or private helper
instances; its target theorem was a single `sorry`.

## New

```lean
import Sheaf.Paper.IntegralReductionFlatFiltration
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.Algebra.Homology.Monoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory integralCoefficientRingSheafify
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  integralTowerHasDerivedCategory integralReductionSourceHasDerivedCategory
  integralReductionTargetHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived integralReductionSiteEssentiallySmall scalarReductionSiteSmall in
-- Applied separately to tor_vanishes and complete_residue_cohomology_bounds.

private theorem abSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

private theorem abLocallyBijective (Y : Scheme.{u}) :
    (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

attribute [local instance] abSheafify abLocallyBijective
```

Instance removal is scoped to each declaration using `in`; the two proved
private helpers are enabled only by `attribute [local instance]`. The lower
filtration module likewise scopes its instance removal with `in`. Thus no
instance-registry change is exported to importers. These commands select the coefficient-sheaf model already used by the target
statement. The theorem signature remains verbatim unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompleteResidueCohomologyBounds | U3 | Proof imports, private helpers and local instance scope only; target statement unchanged. |
| Sheaf.Paper.ResidueLisseProjectiveModels | G2 | Unchanged source compiles against the delivered parent in 4.4 seconds. |
| Sheaf.Paper.FieldStageOrdinaryRealization | U7 | Unchanged source times out both with the delivered parent and with the published parent; baseline slowdown. |
| Sheaf.Paper.IntegralReductionFlatFiltration | U3 | New lower theorem imported privately by the parent proof; its public statement is recorded by node `lem-sf-integral-reduction-flat-filtration`. |

`tools/downstream.py Sheaf.Paper.CompleteResidueCohomologyBounds --uses
complete_residue_cohomology_bounds` lists 211 downstream modules and only the
item itself as a textual declaration user. All existing public signatures and
public imports remain unchanged, so their statements retain their meaning.
The two direct importers are `Sheaf.Paper.ResidueLisseProjectiveModels`
(held by G2) and `Sheaf.Paper.FieldStageOrdinaryRealization` (held by U7).
Their original sources were copied unchanged into isolated scratch verification
packets. ResidueLisseProjectiveModels compiles against the delivered parent in
4.4 seconds. FieldStageOrdinaryRealization reaches the 60-second limit both
against the delivered parent and against the published parent; this is an
existing baseline slowdown. Neither file is adapted.
All public imports of the parent and its existing signature are unchanged.
Neither importer can refer to the private proof helpers. No target definition
changes and no target statement review is reopened.

## Status

landed 20261019T231358-L-579991 2026-10-19 (merge of deliver/U3/Sheaf.Paper.CompleteResidueCohomologyBounds)
