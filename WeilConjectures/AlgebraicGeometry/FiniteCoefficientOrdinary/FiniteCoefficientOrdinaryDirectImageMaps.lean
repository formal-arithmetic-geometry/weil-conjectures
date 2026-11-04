/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived

/-!
# The ordinary étale direct-image coefficient comparison

Source: latest Weil blueprint, sec-smooth-purity/sk-lem-sp-tower,
`lem-coef-finite-direct-image.md` and its proof, Step 3
(blueprint: lem-coef-finite-direct-image).

For `φ : A →+* B` and `f : T ⟶ X`, the derived scalar extension `F = - ⊗ᴸ_A B` commutes with
derived pullback: `F_X ⋙ Lf^* ≅ Lf^* ⋙ F_T`. Both composites are total left derived functors of
the composite `f^*(B ⊗_A -) ≅ B ⊗_A f^* -` of sheaf functors, computed on complexes with K-flat
pullback. The direct-image comparison `c_f : F_X (Rf_* K) ⟶ Rf_* (F_T K)` is the mate of this
isomorphism along the adjunctions `Lf^* ⊣ Rf_*`.

The pullback/scalar isomorphism is
`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`, reproved here
without its unused Noetherian hypothesis on the source ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

-- The braiding of `ModuleCat` found by instance search (`instBraidedCategory`) is not
-- syntactically the one underlying the derived tensor product of étale sheaves; as in
-- `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived`, use the étale one.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.FiniteCoefficientOrdinary

open Etale

section Pullback

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The isomorphism `g^*(S ⊗_R -) ≅ S ⊗_R g^* -` of
`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso`, on homotopy categories. -/
def homotopyExtendScalarsUpperStarIso :
    (sheafExtendScalars φ Y).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ) ≅
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (sheafExtendScalars φ Z).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) _ ≪≫
    { hom := NatTrans.mapHomotopyCategory
        (sheafExtendScalarsCompUpperStarIso φ g).hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory
        (sheafExtendScalarsCompUpperStarIso φ g).inv (.up ℤ)
      hom_inv_id := by simp [← NatTrans.mapHomotopyCategory_comp]
      inv_hom_id := by simp [← NatTrans.mapHomotopyCategory_comp] } ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm

/-- The counit exhibiting `L(S ⊗_R -) ⋙ Lg^*` as a total left derived functor of
`S ⊗_R - ⋙ g^*`. -/
def extendScalarsUpperStarCounit :
    DerivedCategory.Qh ⋙ L(sheafExtendScalars φ Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ⟶
      (sheafExtendScalars φ Y).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (sheafExtendScalars φ Y).leftDerivedFunctorCounit
      L((g)^*[ModuleCat.{u + 1} S]) ≫
    Functor.whiskerLeft ((sheafExtendScalars φ Y).mapHomotopyCategory (.up ℤ))
      (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit

instance isLeftDerivedFunctor_extendScalarsUpperStar :
    (L(sheafExtendScalars φ Y) ⋙ L((g)^*[ModuleCat.{u + 1} S])).IsLeftDerivedFunctor
      (extendScalarsUpperStarCounit φ g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun K ↦ ?_)
  have : IsIso ((sheafExtendScalars φ Y).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.obj K)) :=
    (sheafExtendScalars φ Y).isIso_leftDerivedFunctorCounit_app_of_kFlat
      K.obj.as ((HomotopyCategory.kFlat_quotient_obj_iff _).1 K.property)
  simp only [extendScalarsUpperStarCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance

/-- The counit exhibiting `Lg^* ⋙ L(S ⊗_R -)` as a total left derived functor of
`g^* ⋙ S ⊗_R -`. -/
def upperStarExtendScalarsCounit :
    DerivedCategory.Qh ⋙ L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars φ Z) ⟶
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (sheafExtendScalars φ Z).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit
      L(sheafExtendScalars φ Z) ≫
    Functor.whiskerLeft ((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ))
      (sheafExtendScalars φ Z).leftDerivedFunctorCounit

instance isLeftDerivedFunctor_upperStarExtendScalars :
    (L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars φ Z)).IsLeftDerivedFunctor
      (upperStarExtendScalarsCounit φ g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar (ModuleCat.{u + 1} R) g)) _
    (fun K ↦ ?_)
  have := isIso_leftDerivedFunctorCounit_app_upperStar_mapHomotopyCategory_obj φ g K.obj.as
    K.property
  simp only [upperStarExtendScalarsCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' inferInstance this

/-- Derived extension of scalars commutes with the derived pullback, for an arbitrary map of
coefficient rings: `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S`, induced by `g^*(S ⊗_R F) ≅ S ⊗_R g^* F`.
Source: Stacks 06YY, 0E8I (blueprint: lem-coef-finite-direct-image). -/
def leftDerivedUpperStarExtendScalarsIso :
    L(sheafExtendScalars φ Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ≅
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars φ Z) :=
  Functor.leftDerivedNatIso _ _ (extendScalarsUpperStarCounit φ g)
    (upperStarExtendScalarsCounit φ g)
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (homotopyExtendScalarsUpperStarIso φ g) DerivedCategory.Qh)

/-- The K-flat derived extension of scalars is the fixed derived scalar extension: both are
left adjoint to derived restriction of scalars.
Source: Stacks 06YY (blueprint: lem-coef-finite-direct-image). -/
def leftDerivedExtendScalarsIso (X : Scheme.{u}) :
    L(sheafExtendScalars φ X) ≅
      Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ :=
  (leftDerivedEtaleSheafExtendScalarsAdjunction φ X).leftAdjointUniq
    (scalarAdjunction X.smallEtaleTopology φ)

/-- The fixed derived scalar extension commutes with the derived pullback.
Source: Stacks 06YY, 0E8I (blueprint: lem-coef-finite-direct-image). -/
def scalarExtensionUpperStarIso :
    Sheaf.fixedCoefficientDerivedScalarExtension Y.smallEtaleTopology φ ⋙
        L((g)^*[ModuleCat.{u + 1} S]) ≅
      L((g)^*[ModuleCat.{u + 1} R]) ⋙
        Sheaf.fixedCoefficientDerivedScalarExtension Z.smallEtaleTopology φ :=
  Functor.isoWhiskerRight (leftDerivedExtendScalarsIso φ Y).symm _ ≪≫
    leftDerivedUpperStarExtendScalarsIso φ g ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedExtendScalarsIso φ Z)

end Pullback

/-- The canonical ordinary direct-image coefficient comparisons on small étale sites.
Source: blueprint statement and proof Step 3 (blueprint: lem-coef-finite-direct-image). -/
structure DirectImageMaps where
  /-- The comparison `c_f : F_X ∘ Rf_* ⟶ Rf_* ∘ F_T` on small étale sites. -/
  etale : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X),
    R(Etale.lowerStar (ModuleCat.{u + 1} A) f) ⋙ Sheaf.fixedCoefficientDerivedScalarExtension
      (X.smallEtaleTopology) φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension (T.smallEtaleTopology) φ ⋙ R(Etale.lowerStar
        (ModuleCat.{u + 1} B) f)

/-- The direct-image comparison `c_f`, the mate along `Lf^* ⊣ Rf_*` of the
pullback/scalar-extension isomorphism `F_X ⋙ Lf^* ≅ Lf^* ⋙ F_T`.
Source: blueprint proof Step 3 (blueprint: lem-coef-finite-direct-image). -/
def directImageMaps : DirectImageMaps.{u} where
  etale := fun φ _ _ f ↦
    (mateEquiv (derivedUpperStarLowerStarAdjunction _ f)
      (derivedUpperStarLowerStarAdjunction _ f)
      (TwoSquare.mk _ _ _ _ (scalarExtensionUpperStarIso φ f).hom)).natTrans

end AlgebraicGeometry.FiniteCoefficientOrdinary
