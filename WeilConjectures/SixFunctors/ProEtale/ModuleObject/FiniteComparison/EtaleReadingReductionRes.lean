/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionComparison

/-!
# The commutation of `ν^*` with the derived extension of scalars, in restriction form

Let `φ : Λ →+* Λ'` be a surjective morphism of rings with principal kernel, `Ψ` the derived
extensions of scalars along `φ` of étale and pro-étale sheaves, left adjoint to the restrictions
of scalars `Res`. The commutation `χ : ν^* Ψ ≅ Ψ ν^*`
(`ProEtale.comparisonUpperStarDerivedExtendScalarsIso`) is the mate, under `Ψ ⊣ Res`, of the
commutation `Res ν^* ≅ ν^* Res` of the exact functors `ν^*` and `Res`. This is the form in which
`χ` is used to compute with the base change map of `Rν_*`.

## Main results

- `CategoryTheory.Adjunction.derivedAdjunction_ofNatIsoRight_unit_app_Qh`,
  `CategoryTheory.Adjunction.derivedAdjunction_ofNatIsoRight_counit_app_Qh`: the unit and counit
  of the derived adjunction `Lf ⊣ D(g)` of an adjunction `f ⊣ g` with `g` exact, on the images of
  complexes.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The unit of the derived adjunction `Lf ⊣ D(g)` of an adjunction `f ⊣ g` with `g` exact, on the
image `Qh X` of a complex: modulo the counit of `Lf` and the factorization of `D(g)`, it is the
levelwise unit of `f ⊣ g`. -/
@[reassoc]
lemma derivedAdjunction_ofNatIsoRight_unit_app_Qh (adj : f ⊣ g)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (adj.derivedAdjunction.ofNatIsoRight g.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj X) ≫
      g.mapDerivedCategory.map (f.leftDerivedFunctorCounit.app X) =
    DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X) ≫
      g.mapDerivedCategoryFactorsh.inv.app ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  have h₁ := adj.derivedAdjunction_unit_app_Qh_fac X
  have h₂ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
  have h₃ := g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (f.leftDerivedFunctorCounit.app X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  erw [← h₃, reassoc_of% h₁]
  rw [← h₂]
  rfl

/-- The counit of the derived adjunction `Lf ⊣ D(g)` of an adjunction `f ⊣ g` with `g` exact, on
the image `Qh Z` of a complex: modulo the counit of `Lf` and the factorization of `D(g)`, it is
the levelwise counit of `f ⊣ g`. -/
@[reassoc]
lemma derivedAdjunction_ofNatIsoRight_counit_app_Qh (adj : f ⊣ g)
    (Z : HomotopyCategory D (ComplexShape.up ℤ)) :
    f.leftDerivedFunctor.map (g.mapDerivedCategoryFactorsh.inv.app Z) ≫
      (adj.derivedAdjunction.ofNatIsoRight g.rightDerivedFunctorIsoMapDerivedCategory).counit.app
        (DerivedCategory.Qh.obj Z) =
    f.leftDerivedFunctorCounit.app ((g.mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app Z) := by
  have h₁ := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit Z
  have h₂ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← h₂, ← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact h₁

end Adjunction

end CategoryTheory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/-- The comparison `Res ν^* ⟶ ν^* Res` of the restriction of scalars along `φ` with `ν^*`: the
mate, under the extension–restriction adjunctions, of the commutation
`ν^*(Λ' ⊗_Λ F) ≅ Λ' ⊗_Λ ν^* F` (`comparisonUpperStarCompExtendScalarsIso`). -/
noncomputable def restrictScalarsCompComparisonUpperStar :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ ν^*(X)[ModuleCat.{u + 1} Λ] ⟶
      ν^*(X)[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology X) φ :=
  mateEquiv (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ)
    (Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ)
    (comparisonUpperStarCompExtendScalarsIso φ X).hom

/-- The mate under the adjunctions `ν^* ⊣ ν_*` of `restrictScalarsCompComparisonUpperStar` is the
identity of `ν_* Res = Res ν_*`. -/
lemma mateEquiv_comparisonAdjunction_restrictScalarsCompComparisonUpperStar :
    (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ') X)
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
      (restrictScalarsCompComparisonUpperStar φ X)).natTrans = 𝟙 _ := by
  rw [restrictScalarsCompComparisonUpperStar, iterated_mateEquiv_conjugateEquiv]
  exact Equiv.apply_symm_apply _ _

section

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R]
  [CommRing S] (f : R →+* S)

lemma _root_.CategoryTheory.Sheaf.restrictCoextendScalarsAdj_unit_app_hom_app
    (F : Sheaf J (ModuleCat.{u + 1} S)) (U : Cᵒᵖ) :
    ((Sheaf.restrictCoextendScalarsAdj J f).unit.app F).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} f).unit.app (F.obj.obj U) := by
  have h := NatTrans.congr_app (Adjunction.map_restrictFullyFaithful_unit_app
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} f).whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _)
    (L := Sheaf.restrictScalars J f) (R := sheafCompose J (ModuleCat.coextendScalars f)) (Iso.refl _)
    (Iso.refl _) F) U
  simpa [Sheaf.restrictCoextendScalarsAdj] using h

lemma _root_.CategoryTheory.Sheaf.restrictCoextendScalarsAdj_counit_app_hom_app
    (F : Sheaf J (ModuleCat.{u + 1} R)) (U : Cᵒᵖ) :
    ((Sheaf.restrictCoextendScalarsAdj J f).counit.app F).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} f).counit.app (F.obj.obj U) := by
  have h := NatTrans.congr_app (Adjunction.map_restrictFullyFaithful_counit_app
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} f).whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _)
    (L := Sheaf.restrictScalars J f) (R := sheafCompose J (ModuleCat.coextendScalars f)) (Iso.refl _)
    (Iso.refl _) F) U
  refine h.trans ?_
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

end

/-- The mate, under the restriction–coextension adjunctions, of the identity of `ν_* Res = Res ν_*`
is the identity of `ν_* Coext = Coext ν_*`: all four functors are computed sectionwise, and this is
a triangle identity of `Res ⊣ Coext` on modules. -/
lemma mateEquiv_restrictCoextendScalarsAdj_id :
    (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ)
      (TwoSquare.mk (ν_*(X)[ModuleCat.{u + 1} Λ']) (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
        (Sheaf.restrictScalars X.smallEtaleTopology φ) (ν_*(X)[ModuleCat.{u + 1} Λ])
        (𝟙 _))).natTrans = 𝟙 _ := by
  ext M : 2
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  ext U : 2
  simp [mateEquiv, Sheaf.restrictCoextendScalarsAdj_unit_app_hom_app,
    Sheaf.restrictCoextendScalarsAdj_counit_app_hom_app, comparisonLowerStar]
  erw [Category.id_comp]
  exact (ModuleCat.restrictCoextendScalarsAdj φ).right_triangle_components _

/-- **The comparison `Res ν^* ⟶ ν^* Res` is an isomorphism**: by the calculus of iterated mates,
it is conjugate to the mate of the identity of `ν_* Res = Res ν_*` under the
restriction–coextension adjunctions, the identity of `ν_* Coext = Coext ν_*`
(`mateEquiv_restrictCoextendScalarsAdj_id`). -/
instance isIso_restrictScalarsCompComparisonUpperStar :
    IsIso (restrictScalarsCompComparisonUpperStar φ X) := by
  have h := iterated_mateEquiv_conjugateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ') X)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (restrictScalarsCompComparisonUpperStar φ X)
  have h₁ : mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ') X)
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X) (restrictScalarsCompComparisonUpperStar φ X) =
        TwoSquare.mk (ν_*(X)[ModuleCat.{u + 1} Λ']) (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
          (Sheaf.restrictScalars X.smallEtaleTopology φ) (ν_*(X)[ModuleCat.{u + 1} Λ]) (𝟙 _) :=
    mateEquiv_comparisonAdjunction_restrictScalarsCompComparisonUpperStar φ X
  rw [h₁, mateEquiv_restrictCoextendScalarsAdj_id] at h
  have : IsIso (conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} Λ') X).comp
        (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ))
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
        (comparisonAdjunction (ModuleCat.{u + 1} Λ) X))
      (restrictScalarsCompComparisonUpperStar φ X)) := by
    rw [← h]
    infer_instance
  have := conjugateEquiv_symm_iso
    ((comparisonAdjunction (ModuleCat.{u + 1} Λ') X).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ))
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) X))
    (conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} Λ') X).comp
        (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ))
      ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
        (comparisonAdjunction (ModuleCat.{u + 1} Λ) X))
      (restrictScalarsCompComparisonUpperStar φ X))
  rwa [Equiv.symm_apply_apply] at this

/-- The commutation `Res ν^* ≅ ν^* Res` of the exact functors `ν^*` and `Res`, on derived
categories (`restrictScalarsCompComparisonUpperStar`). -/
noncomputable def derivedRestrictScalarsCompComparisonUpperStarIso :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ']) ⋙ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ :=
  Functor.mapDerivedCategorySquareIso (asIso (restrictScalarsCompComparisonUpperStar φ X))

end AlgebraicGeometry.ProEtale
