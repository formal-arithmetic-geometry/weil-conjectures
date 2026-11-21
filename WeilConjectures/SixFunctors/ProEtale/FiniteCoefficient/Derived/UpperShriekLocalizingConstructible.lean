/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureRightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing

/-!
# The exceptional inverse image on `Loc(Dctf)` restricts to `Dctf`, finite coefficients

Let `Λ` be a finite ring and `k` a field of finite cohomological dimension for `Λ`-modules. For a
compactification `c` of a morphism `f : X ⟶ Y` of separated finite-type `k`-schemes on which the
exponent of `Λ` is invertible, consider the compact-support direct image
`Rf_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekLocalizing`) and its right adjoint `f^!`
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriekLocalizing`), given by Brown
representability.

## Main statements

- `AlgebraicGeometry.ProEtale.isTriangulated_rightDerivedLowerShriekLocalizing`,
  `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerivedLowerShriekLocalizing`:
  `Rf_!` is triangulated and preserves direct sums.
- `AlgebraicGeometry.ProEtale.isTriangulated_rightDerivedUpperShriekLocalizing`: `f^!` is
  triangulated.
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj`:
  `f^!` maps `Dctf(Y, Λ)` into `Dctf(X, Λ)`.
- `AlgebraicGeometry.ProEtale.constructibleFiniteTorUpperShriekLocalizingAdjunction`: the
  adjunction `Rf_! ⊣ f^!` restricts to `Dctf`.

## Implementation details

On `Dctf`, `Rf_!(c)` is identified with the compact-support direct image for the chosen
compactification
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso`),
which has a right adjoint on `Dctf`
(`AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction`). Since
the objects of `Dctf(X, Λ)` detect isomorphisms of `Loc(Dctf(X, Λ))`, `f^!` agrees on `Dctf(Y, Λ)`
with that right adjoint (`CategoryTheory.ObjectProperty.prop_rightAdjoint_obj_of_isLeftAdjoint`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

section LowerShriek

variable {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)

/-- The compact-support direct image `Rf_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))` attached to a
compactification is triangulated. -/
theorem isTriangulated_rightDerivedLowerShriekLocalizing :
    (rightDerivedLowerShriekLocalizing Λ aY c).IsTriangulated :=
  inferInstance

/-- The compact-support direct image `Rf_! : Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))` attached to a
compactification preserves direct sums. -/
theorem preservesColimitsOfShape_rightDerivedLowerShriekLocalizing (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedLowerShriekLocalizing Λ aY c) :=
  inferInstance

end LowerShriek

section UpperShriek

variable (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] [HasInvertibleExponent Λ X]
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] [HasInvertibleExponent Λ Y] {f : X ⟶ Y} (c : Compactification f)

/-- The exceptional inverse image `f^! : Loc(Dctf(Y, Λ)) ⥤ Loc(Dctf(X, Λ))` is triangulated. -/
theorem isTriangulated_rightDerivedUpperShriekLocalizing :
    (rightDerivedUpperShriekLocalizing Λ hk aX aY c).IsTriangulated :=
  inferInstance

/-- The exceptional inverse image `f^! : Loc(Dctf(Y, Λ)) ⥤ Loc(Dctf(X, Λ))` maps `Dctf(Y, Λ)` into
`Dctf(X, Λ)`. -/
theorem constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj
    (L : DerivedCategoryLocalizingFiniteTor Λ Y)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L.obj) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((rightDerivedUpperShriekLocalizing Λ hk aX aY c).obj L).obj := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
  have := c.hasCompactification
  have : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K hK ↦ hK.shift n⟩⟩
  let PX := DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
  let PY := DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
  -- `Rf_!(c)` on `Dctf`
  let Fb : PX.FullSubcategory ⥤ PY.FullSubcategory := PY.lift
    (PX.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c)
    fun K ↦ constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c K.property
  let adj := DerivedCategoryFiniteTor.rightDerivedLowerShriekAdjunction Λ aY f
  have := adj.isLeftAdjoint
  -- it agrees with the compact-support direct image for the chosen compactification
  let e : PX.ι ⋙ ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ≅
      PX.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c :=
    Functor.isoWhiskerLeft (ObjectProperty.ιOfLE fun _ h ↦ h.plusEtaleOrigin)
      (rightDerivedLowerShriekOfCompactificationEtaleOriginIso Λ
        (HasCompactification.compactification f) c)
  have : Fb.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso
    ((PY.fullyFaithfulι.whiskeringRight _).preimageIso
      (PY.liftCompιIso _ _ ≪≫ e ≪≫ (PY.liftCompιIso _ _).symm))
  exact ObjectProperty.prop_rightAdjoint_obj_of_isLeftAdjoint
    (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c)
    (ObjectProperty.fullyFaithfulιOfLE (ObjectProperty.le_localizingClosure PY)) Fb (Iso.refl _)
    ⟨L.obj, hL⟩

/-- The adjunction `Rf_! ⊣ f^!` on `Loc(Dctf)` restricts to the full subcategories `Dctf`. -/
noncomputable def constructibleFiniteTorUpperShriekLocalizingAdjunction :
    ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).inverseImage
        (DerivedCategory.localizingConstructibleFiniteTor Λ Y).ι).lift
        (((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage
          (DerivedCategory.localizingConstructibleFiniteTor Λ X).ι).ι ⋙
            rightDerivedLowerShriekLocalizing Λ aY c)
        (fun K ↦ constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c
          K.property) ⊣
      ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage
        (DerivedCategory.localizingConstructibleFiniteTor Λ X).ι).lift
        (((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).inverseImage
          (DerivedCategory.localizingConstructibleFiniteTor Λ Y).ι).ι ⋙
            rightDerivedUpperShriekLocalizing Λ hk aX aY c)
        (fun L ↦ constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj Λ hk aX aY c
          L.obj L.property) :=
  (rightDerivedUpperShriekLocalizingAdjunction Λ hk aX aY c).restrictObjectProperty _ _
    (fun _ hK ↦ constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c hK)
    (constructibleFiniteTor_rightDerivedUpperShriekLocalizing_obj Λ hk aX aY c)

end UpperShriek

end AlgebraicGeometry.ProEtale
