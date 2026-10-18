/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.SecondStep
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients

/-!
# The constant coefficients `Λ/dΛ` and the base-change map

Auxiliary statements about the constant sheaf `Λ/dΛ`
(`AlgebraicGeometry.Etale.constantModSheaf`) used in the proof of
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_field`:

- it is constructible when `Λ` is finite
  (`AlgebraicGeometry.Etale.isConstructibleSheaf_constantModSheaf`);
- its pullback along any morphism is the constant sheaf `Λ/dΛ`
  (`AlgebraicGeometry.Etale.upperStarConstantModSheafIso`);
- whether a base-change map is an isomorphism only depends on the isomorphism class of the
  coefficient sheaf (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_iso`);
- if the base-change map of a square at the constant sheaf `Λ/dΛ` is an isomorphism and
  `R^q g_* (Λ/dΛ)` vanishes, then so does `R^q h_* (Λ/dΛ)`
  (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isIso_baseChangeHomologyMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Limits of size `u` exist in `ModuleCat.{u + 1} Λ`. -/
local instance hasLimitsOfSizeModuleCat_constantModSheaf :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- The forgetful functor of `ModuleCat.{u + 1} Λ` preserves filtered colimits of size `u`. -/
local instance preservesFilteredColimits_constantModSheaf :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- The constant sheaf `Λ/dΛ` is finite locally constant when `Λ` is finite: it is constant, and
its stalks are all `Λ/dΛ`. -/
instance Etale.isFiniteLocallyConstantSheaf_constantModSheaf [Finite Λ] (X : Scheme.{u})
    (d : ℕ) : Scheme.IsFiniteLocallyConstantSheaf (Etale.constantModSheaf Λ X d) where
  toIsLocallyConstantSheaf := Etale.isLocallyConstantSheaf_constantSheaf _
  toIsFiniteSheaf := ⟨fun _ _ _ s ↦
    ((ModuleCat.isFinitelyGenerated_iff
      (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)))).2 inferInstance).of_iso
      ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso _).symm⟩

/-- The constant sheaf `Λ/dΛ` is constructible when `Λ` is finite. -/
instance Etale.isConstructibleSheaf_constantModSheaf [Finite Λ] (X : Scheme.{u}) (d : ℕ) :
    Scheme.IsConstructibleSheaf (Etale.constantModSheaf Λ X d) :=
  Scheme.IsConstructibleSheaf.of_isFiniteLocallyConstantSheaf _

/-- The pullback of the constant sheaf `Λ/dΛ` is the constant sheaf `Λ/dΛ`. -/
noncomputable def Etale.upperStarConstantModSheafIso {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (f)^*[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ Y d) ≅
      Etale.constantModSheaf Λ X d :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).app _

section BaseChange

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Whether the degree-`q` base-change map at a sheaf is an isomorphism only depends on the
isomorphism class of the sheaf, by naturality of the base-change map. -/
lemma Etale.isIso_baseChangeHomologyMap_iff_of_iso (sq : IsPullback e h g p) (q : ℤ)
    {F F' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ≅ F') :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) ↔
      IsIso (Etale.baseChangeHomologyMap Λ sq q F') :=
  NatTrans.isIso_app_iff_of_iso (Etale.baseChangeHomologyNatTrans Λ sq q) α

/-- If the degree-`q` base-change map of a Cartesian square at the constant sheaf `Λ/dΛ` is an
isomorphism and `R^q g_* (Λ/dΛ)` vanishes, then so does `R^q h_* (Λ/dΛ)`: the source
`p⁻¹ R^q g_* (Λ/dΛ)` vanishes, hence so does the target `R^q h_* e⁻¹ (Λ/dΛ)`, and `e⁻¹ (Λ/dΛ)`
is the constant sheaf `Λ/dΛ`. -/
theorem Etale.isZero_higherDirectImage_of_isIso_baseChangeHomologyMap
    (sq : IsPullback e h g p) (q : ℤ) (d : ℕ)
    (hg : IsZero (Etale.higherDirectImage Λ g q (Etale.constantModSheaf Λ T d)))
    (hsq : IsIso (Etale.baseChangeHomologyMap Λ sq q (Etale.constantModSheaf Λ T d))) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  have hsource : IsZero ((Etale.baseChangeSourceFunctor Λ p g q).obj
      (Etale.constantModSheaf Λ T d)) :=
    IsZero.of_iso (((p)^*[ModuleCat.{u + 1} Λ]).map_isZero hg)
      ((Etale.baseChangeSourceFunctorIso Λ p g q).app _)
  have htarget : IsZero ((DerivedCategory.Plus.singleFunctor _ 0 ⋙
      R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q).obj
        ((e)^*[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ T d))) :=
    (hsource.of_iso (asIso (Etale.baseChangeHomologyMap Λ sq q _)).symm).of_iso
      ((Etale.baseChangeTargetFunctorIso Λ e h q).app _).symm
  exact htarget.of_iso ((DerivedCategory.Plus.singleFunctor _ 0 ⋙
    R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (Etale.upperStarConstantModSheafIso Λ e d)).symm

end BaseChange

end AlgebraicGeometry
