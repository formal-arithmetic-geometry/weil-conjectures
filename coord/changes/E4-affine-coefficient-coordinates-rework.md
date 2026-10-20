# AlgebraicGeometry.coefficientCoordinatesAbelian

## Reason

Restore the proved module archived by the 2026-10-20 upstream sync at the path
recorded in `coord/rework.tsv`. The archived local Abelian instance leaves the
module universe unconstrained and fails to synthesize
`(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat`.
Request the existing instance on `SheafOfModules.{u}` explicitly, as in the
corresponding adopted source module and the repaired factorization dependency.

The current factorization theorem displays its derived unit using scheme
pushforward rather than ringed-space module direct image. Reduce the
definitions of the two pushforward functors and their underlying sheaf-ring
morphism presentations before applying the factorization.
This preserves the archived public theorem statement verbatim, including its
ringed-space derived unit, all binders, and universes.

## Old

```lean
local instance (priority := 2000) coefficientCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := SheafOfModules.instAbelian Y.ringCatSheaf
```

Final proof steps:

```lean
  have h := affineTildePushforwardHomologyFactorization D B ψ Cg i _ v
  simpa only [v, Functor.map_comp, Category.assoc] using h
```

## New

```lean
local instance (priority := 2000) coefficientCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
```

Final proof steps:

```lean
  have h := affineTildePushforwardHomologyFactorization D B ψ Cg i _ v
  dsimp only [Scheme.Modules.pushforward, Scheme.Hom.toRingCatSheafHom,
    RingedSpace.moduleDirectImage, Scheme.Hom.toLRSHom,
    LocallyRingedSpace.Hom.toShHom, InducedCategory.homMk] at h ⊢
  simpa only [v, Functor.map_comp, Category.assoc] using h
```

## Users

`python3 tools/downstream.py
Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates
--allow-missing --uses affineTildeCoefficientPushforwardHomologyCoordinates`
reports zero live downstream modules and zero live declaration users. Searching
`lean/`, `quarantine/`, and the DAG retains the parent listed below; its unfinished
restoration is a separate rework item. The current claim directory has no claim
for that parent. The source-library counterpart has a separate source-library
import path and is not changed by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorHomologyCoordinates | unclaimed, quarantined | Uses the unchanged theorem at the final proof step; no adaptation required. |

The theorem signature and both imports remain byte-for-byte unchanged from the
archive. No definition appearing in a target statement changes. The module's DAG
attachment, dependencies, and unit route remain intact. The node proof and
proof-origin note explain the explicit functor-equality conversion.

An independent consumer module in the sandbox scratchpad restates the complete
archived public theorem signature and proves it by applying the restored theorem.
The repaired module compiles in 41.1 seconds and the consumer in 14.1 seconds.
`#print axioms` for both declarations lists exactly `propext`, `Classical.choice`,
and `Quot.sound`. The original archived file reproduces both the instance error
and the proof's derived-unit presentation mismatch. The delivery dry run passes
compilation and server preflight with review class CODEX.

## Status

landed 20261020T160257-L-3349992 2026-10-20 (merge of deliver/E4/Sheaf.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates)
