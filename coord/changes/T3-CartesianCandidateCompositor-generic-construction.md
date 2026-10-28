# AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly.candidateCompositor

## Reason

Expanding the concrete four-factor body in a component equality cost 95 seconds
of kernel checking and hit a deterministic timeout. Use the existing generic
`finiteSupportCandidateCompositionCore` with the same four maps. Comparing
the two applications of the generic core only requires congruence in its final
comparison argument, without expanding concrete category composition. The last input is the inverse of the existing forward comparison,
so its inverse component is exactly that forward comparison.

The signature and four specified maps are unchanged. The construction chooses no
new data and changes no target meaning. Its public body needs the added public
import `Sheaf.Paper.FiniteSupportCandidateComposition`. The module is unclaimed
in the current shared claim records. The import-direction check permits this edge.

## Old

```lean
def candidateCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf).obj K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg).obj K.obj :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).map
      ((towerCandidateComparison Λ cf (HasCompactification.compactification f)).hom.app K) ≫
    (towerCandidateComparison Λ cg (HasCompactification.compactification g)).hom.app
      ((originCompactSupport Λ f).obj K) ≫
    (originCompositionAmbient Λ f g).hom.app K ≫
    (towerCandidateComparison Λ (HasCompactification.compactification (f ≫ g)) cfg).hom.app K
```

## New

```lean
def candidateCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf).obj K.obj) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg).obj K.obj :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  (WeilConjectures.CompactSupportFiniteProjection.finiteSupportCandidateCompositionCore
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X).ι
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y).ι
    (originCompactSupport Λ f)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g))
    (towerCandidateComparison Λ cf (HasCompactification.compactification f))
    (towerCandidateComparison Λ cg (HasCompactification.compactification g))
    (originCompositionAmbient Λ f g)
    (towerCandidateComparison Λ (HasCompactification.compactification (f ≫ g)) cfg).symm).hom.app K
```

## Users

The rows include every declaration user reported by `tools/downstream.py --uses`,
and the item using the new component calculation. No consumer source is changed.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctors.CartesianCandidateCompositor` | unclaimed | Same signature and four factors; construction factored through existing generic core. |
| `Sheaf.SixFunctors.CartesianCandidateSiteSquare` | unclaimed | Source unchanged; compile against the new constructor. |
| `Sheaf.SixFunctors.CartesianCompactSupportCompositor` | unclaimed | Source unchanged; compile against the new constructor. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed | Source unchanged; compile the indirect user against the new constructor. |
| `Sheaf.Paper.FiniteProjectionCompositionEndpointProofs` | T3 | Compare applications of the generic core by congruence in the endpoint proof. |
| `Sheaf.Paper.FiniteProjectionCompositionRealization` | T3 | Use the proved endpoint normalization through the helper module. |

## Status

landed 20261028T055804-L-809833 2026-10-28 (merge of deliver/T3/Sheaf.Paper.FiniteProjectionCompositionRealization)
