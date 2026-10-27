# AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly.candidateCompositor

## Reason

The Cartesian raw-mate proof and the canonical site square must share this constructor.
Duplicating its four factors caused a kernel deterministic timeout (91 seconds) merely
checking the definitional equality with the existing constructor. Move the declaration
verbatim into a shared construction module. Its name, signature, attributes and body
are unchanged; the original item publicly imports the new module. No target meaning changes.

## Old

Declared in `Sheaf.SixFunctors.CartesianCompactSupportCompositor`:

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

The identical declaration is in `Sheaf.SixFunctors.CartesianCandidateCompositor`;
the original item publicly imports that module. The canonical site-square statement
uses this same named constructor instead of a duplicate of its body.

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

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | F5 | Publicly reexports the identical declaration; proof uses its shared name. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Existing name, signature and body remain available; compiled unchanged against the relocation. |
| Sheaf.SixFunctors.CartesianCandidateSiteSquare | F5 | Uses the shared constructor in its new statement. |

## Status

landed 20261027T034638-L-3669558 2026-10-27 (merge of deliver/F5/Sheaf.SixFunctors.CartesianCompactSupportCompositor)
