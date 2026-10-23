/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Extension of scalars commutes with the derived pullback

Let `φ : A →+* B` be a surjective morphism of commutative rings with principal kernel and
`f : X ⟶ Y` a morphism of schemes. The derived extension of scalars `- ⊗ᴸ_A B` commutes with the
derived pullback: `(Lf^* K) ⊗ᴸ_A B ≅ Lf^*(K ⊗ᴸ_A B)`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedExtendScalars_leftDerivedUpperStar`).

At the level of sheaves, `B ⊗_A f^* F ≅ f^*(B ⊗_A F)`, both functors being left adjoint to
`F ↦ f_* Res F = Res f_* F`. On derived categories, both composites are total left derived
functors of `F ↦ B ⊗_A f^* F`: they are computed on K-flat complexes `P` with `f^* P` K-flat,
which form a left derivability structure.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Sheaves of modules on the small étale site have countable coproducts. Instance search times
out on this. -/
local instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
  (hφ : Function.Surjective φ) {a : A} (ha : RingHom.ker φ = Ideal.span {a})
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Extension of scalars of étale sheaves commutes with the pullback:
`B ⊗_A f^* F ≅ f^*(B ⊗_A F)`, both being left adjoint to `F ↦ f_* Res F = Res f_* F`. -/
noncomputable def extendScalarsUpperStarIso :
    Sheaf.extendScalars Y.smallEtaleTopology φ ⋙ (f)^*[ModuleCat.{u + 1} B] ≅
      (f)^*[ModuleCat.{u + 1} A] ⋙ Sheaf.extendScalars X.smallEtaleTopology φ :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ))
    ((Sheaf.extendScalarsAdjunction Y.smallEtaleTopology φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
    (lowerStarCompRestrictScalarsIso φ f).symm

/-- The counit exhibiting `Lf^* ⋙ (- ⊗ᴸ_A B)` as a left derived functor of
`F ↦ B ⊗_A f^* F`. -/
noncomputable def upperStarExtendScalarsCounit :
    DerivedCategory.Qh ⋙ (L((f)^*[ModuleCat.{u + 1} A]) ⋙ derivedExtendScalars hφ ha X) ⟶
      ((f)^*[ModuleCat.{u + 1} A] ⋙ Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (f)^*[ModuleCat.{u + 1} A].leftDerivedFunctorCounit
      (derivedExtendScalars hφ ha X) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((f)^*[ModuleCat.{u + 1} A].mapHomotopyCategory (ComplexShape.up ℤ))
      (Sheaf.extendScalars X.smallEtaleTopology φ).leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh

/-- The counit exhibiting `(- ⊗ᴸ_A B) ⋙ D(f^*)` as a left derived functor of
`F ↦ B ⊗_A f^* F ≅ f^*(B ⊗_A F)`. -/
noncomputable def extendScalarsUpperStarCounit :
    DerivedCategory.Qh ⋙ (derivedExtendScalars hφ ha Y ⋙ D((f)^*[ModuleCat.{u + 1} B])) ⟶
      ((f)^*[ModuleCat.{u + 1} A] ⋙ Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  have := preservesKFlatQuasiIso_extendScalars hφ ha Y
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Sheaf.extendScalars Y.smallEtaleTopology φ).leftDerivedFunctorCounit
      D((f)^*[ModuleCat.{u + 1} B]) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((Sheaf.extendScalars Y.smallEtaleTopology φ).mapHomotopyCategory (ComplexShape.up ℤ))
      (f)^*[ModuleCat.{u + 1} B].mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (extendScalarsUpperStarIso f)
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh

include hφ ha in
/-- **Extension of scalars commutes with the derived pullback**:
`(Lf^* K) ⊗ᴸ_A B ≅ Lf^*(K ⊗ᴸ_A B)` for `K ∈ D(Y_ét, A)`. Both composites are total left derived
functors of `F ↦ B ⊗_A f^* F` (`AlgebraicGeometry.Etale.extendScalarsUpperStarIso`), the counits
being isomorphisms on K-flat complexes `P` with `f^* P` K-flat. -/
theorem nonempty_iso_derivedExtendScalars_leftDerivedUpperStar
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Nonempty ((derivedExtendScalars hφ ha X).obj ((L((f)^*[ModuleCat.{u + 1} A])).obj K) ≅
      (L((f)^*[ModuleCat.{u + 1} B])).obj ((derivedExtendScalars hφ ha Y).obj K)) := by
  have := preservesKFlatQuasiIso_extendScalars hφ ha X
  have := preservesKFlatQuasiIso_extendScalars hφ ha Y
  let Φ := HomotopyCategory.quasiIsoLocalizerMorphism (f)^*[ModuleCat.{u + 1} A].kFlatInterKFlatMap
  have h₁ : (L((f)^*[ModuleCat.{u + 1} A]) ⋙ derivedExtendScalars hφ ha X).IsLeftDerivedFunctor
      (upperStarExtendScalarsCounit hφ ha f) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure Φ _ fun P ↦ ?_
    have := (f)^*[ModuleCat.{u + 1} A].isIso_leftDerivedFunctorCounit_app_of_kFlat' _ P.property.1
    simp only [upperStarExtendScalarsCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp]
    refine IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' ?_ inferInstance)
    exact Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat'
      (Sheaf.extendScalars X.smallEtaleTopology φ)
      (((f)^*[ModuleCat.{u + 1} A].mapHomotopyCategory (ComplexShape.up ℤ)).obj (Φ.functor.obj P))
      P.property.2
  have h₂ : (derivedExtendScalars hφ ha Y ⋙ D((f)^*[ModuleCat.{u + 1} B])).IsLeftDerivedFunctor
      (extendScalarsUpperStarCounit hφ ha f) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure Φ _ fun P ↦ ?_
    have := Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat'
      (Sheaf.extendScalars Y.smallEtaleTopology φ) (Φ.functor.obj P) P.property.1
    simp only [extendScalarsUpperStarCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance
  let e := Functor.leftDerivedUnique _ _ (upperStarExtendScalarsCounit hφ ha f)
    (extendScalarsUpperStarCounit hφ ha f) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  exact ⟨e.app K ≪≫ ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app _).symm⟩

end Etale

end AlgebraicGeometry
