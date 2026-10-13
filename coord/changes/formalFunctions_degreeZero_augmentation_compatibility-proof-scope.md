# formalFunctions_degreeZero_augmentation_compatibility

## Reason

The static interface checker treats new elaboration commands as an interface change.
The canonical degree-zero component construction imported from SystemIso needs
local registration of the existing Scheme.Modules.enoughInjectives theorem, and the same
transparency settings as the already landed FormalFunctionsDegreeZeroSystemIso proof.
These commands affect this file's proof elaboration. Existing public signatures and
public imports remain identical. No definition used in a target changes.

## Old

```lean
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
```

The existing public signature is:

```lean
theorem formalFunctions_degreeZero_augmentation_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
              ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
                (SheafOfModules.unit X.ringCatSheaf))).hom (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
```

The existing public signature remains:

```lean
theorem formalFunctions_degreeZero_augmentation_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
              ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
                (SheafOfModules.unit X.ringCatSheaf))).hom (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t
```

No private helpers are redeclared: `import all` exposes the existing private zeroIso,
levelIso and levelIso_naturality from FormalFunctionsDegreeZeroSystemIso to this proof.
The added
FormalFunctionsDegreeZeroAugmentedSections theorem is in its own new module and is
imported only for the proof. No proof-local constant enters a public signature.

## Users

The read-only downstream check found 229 downstream modules and two textual users
of formalFunctions_degreeZero_augmentation_compatibility, listed below. There is
no semantic interface change, so no original importer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility | V1 | Own proof gains local settings and imports canonical components; signature identical. |
| Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroCompatibility | unclaimed | The obtain of b and its compatibility proof has its original type; no edit required. |

All remaining downstream importers see the same existing public signature and
public statement dependencies. No target review is reopened: no target or
statement-level definition changes, and no new global instance is exported.

## Status

landed 20261013T054242-L-450807 2026-10-13 (merge of deliver/V1/Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility)
