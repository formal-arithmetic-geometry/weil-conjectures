/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantScalarTowerAdjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedExactSquareCoherence
import all WeilConjectures.SixFunctors.ExactLocalizationInverseMate
import all WeilConjectures.SixFunctors.AmbientOrdinaryClopenLocalization
import all WeilConjectures.AlgebraicGeometry.OrdinaryOpenScalarComposition

/-! # Adjunction normalization of constant scalar tower associativity

Source: Stacks 07A6 and 0940; strict scalar composition, auxiliary Steps 2--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

private theorem rightDerived_unit_exact
    {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (P : CochainComplex A ℤ) :
    R.rightDerivedFunctorUnitQ P ≫
        R.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P) =
      R.mapDerivedCategoryFactors.inv.app P := by
  have h := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient _ _).obj P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorUnitQ, Category.assoc]
  have qh : (DerivedCategory.quotientCompQhIso A).hom.app P = 𝟙 _ := rfl
  have qi : (DerivedCategory.quotientCompQhIso B).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [qh, qi]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  erw [h]
  have hi : R.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ _).obj P) = R.mapDerivedCategoryFactors.app P :=
    Iso.ext (AlgebraicGeometry.ProEtale.AmbientClopen.factorsh_hom R P)
  exact congrArg Iso.inv hi

private theorem exactAdjunction_eq
    {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory = a.mapExactDerivedCategory := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro P
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P))).mp
  change (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      R.rightDerivedFunctorIsoMapDerivedCategory).homEquiv _ _
      (L.mapDerivedCategoryFactors.hom.app P) =
    a.mapExactDerivedCategory.homEquiv _ _ (L.mapDerivedCategoryFactors.hom.app P)
  have hd := CategoryTheory.ExactDerivedSquare.cochain_hom_formula R L a P
    ((L.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  have he := CategoryTheory.exact_hom_fac a P
    ((L.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hd
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at he
  have hd' : a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (L.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ (𝟙 _)) ≫
        R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
    exact hd
  have he' : a.mapExactDerivedCategory.homEquiv _ _
        (L.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ (𝟙 _)) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
    exact he
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, hd', Category.assoc]
  erw [rightDerived_unit_exact]
  exact he'.symm

private theorem whisker_associator
    {A B C J : Type*} [Category A] [Category B] [Category C] [Category J]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {R : B ⥤ A} {S : C ⥤ B} {V : C ⥤ A}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ V) (ρ : S ⋙ R ≅ V) :
    (Functor.whiskeringRight J A C).mapIso (Adjunction.leftAdjointCompIso a b c ρ) =
      Adjunction.leftAdjointCompIso (a.whiskerRight J) (b.whiskerRight J)
        (c.whiskerRight J) ((Functor.whiskeringRight J C A).mapIso ρ) := by
  apply Iso.ext
  ext N n
  simp [Adjunction.leftAdjointCompIso, conjugateIsoEquiv_symm_apply_hom,
    conjugateEquiv_symm_apply_app, Adjunction.comp_counit_app]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

/-- The identity-on-sections compositor for ordinary scalar restriction on towers.
Source: Stacks 03DA and 0940
(blueprint: lem-pur-strict-scalar-tower-associator). -/
def towerScalarRestrictionCompositionOrdinary (W : Scheme.{u}) :
    restrict l F L j W ⋙ restrict l E F i W ≅ restrict l E L (j.comp i) W :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (pbcRestrictComp _ _ _ (by
    unfold constantMap
    rw [← Functor.map_comp]
    congr 1))

/-- Exact localization of the scalar restriction compositor.
Source: Stacks 0940 (blueprint: lem-pur-strict-scalar-tower-associator). -/
def towerScalarRestrictionComposition (W : Scheme.{u}) :
    U l F L j W ⋙ U l E F i W ≅ U l E L (j.comp i) W :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (towerScalarRestrictionCompositionOrdinary l E F i L j W)

/-- The localized ordinary scalar associator preserves the specified derived units.
Source: Stacks 07A6 and 0940; auxiliary Steps 2--3 of strict scalar composition
(blueprint: lem-pur-strict-scalar-tower-associator).

Proof: the ordinary associator is left-adjoint uniqueness after transporting the
composite adjunction along the identity-on-sections restriction compositor.
Consequently its transpose carries the successive scalar units to the direct
unit. Whisker this equality by the tower index category and apply it termwise to
complexes. Exact localization preserves the equality, using the canonical
mapDerivedCategoryCompIso and mapDerivedCategoryFactors. The exact derived scalar
adjunction is the right-derived adjunction transported by
rightDerivedFunctorIsoMapDerivedCategory: both have this same localized unit.
Uniqueness of an adjunction from its unit identifies these adjunctions. Finally
leftAdjointCompIso is uniquely characterized by preservation of these units,
which proves the displayed equality. This applies to zero towers, empty schemes,
identity embeddings and unbounded complexes, without any completeness assumption. -/
theorem scalarTowerAssociator_normalization (W : Scheme.{u}) :
    (haveI := (tensor_exact l E F i W).1
     have := (tensor_exact l E F i W).2
     have := (tensor_exact l F L j W).1
     have := (tensor_exact l F L j W).2
     have := (tensor_exact l E L (j.comp i) W).1
     have := (tensor_exact l E L (j.comp i) W).2
     (Functor.mapDerivedCategoryCompIso (tensor l E F i W) (tensor l F L j W)).symm ≪≫
       Functor.mapDerivedCategoryNatIso
         ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
           ((((pbcScalarAdjunction (constantMap l E F i W)).comp
             (pbcScalarAdjunction (constantMap l F L j W))).ofNatIsoRight
             (pbcRestrictComp _ _ _ (by
               unfold constantMap
               rw [← Functor.map_comp]
               congr 1))).leftAdjointUniq
             (pbcScalarAdjunction (constantMap l E L (j.comp i) W))))) =
      Adjunction.leftAdjointCompIso (scalarAdj l E F i W) (scalarAdj l F L j W)
        (scalarAdj l E L (j.comp i) W)
        (towerScalarRestrictionComposition l E F i L j W) := by
  have := (tensor_exact l E F i W).1
  have := (tensor_exact l E F i W).2
  have := (tensor_exact l F L j W).1
  have := (tensor_exact l F L j W).2
  have := (tensor_exact l E L (j.comp i) W).1
  have := (tensor_exact l E L (j.comp i) W).2
  let a := pbcScalarAdjunction (constantMap l E F i W)
  let b := pbcScalarAdjunction (constantMap l F L j W)
  let c := pbcScalarAdjunction (constantMap l E L (j.comp i) W)
  let ρ := pbcRestrictComp (constantMap l E F i W) (constantMap l F L j W)
    (constantMap l E L (j.comp i) W) (by
      unfold constantMap
      rw [← Functor.map_comp]
      congr 1)
  have hordinary :
      (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
          (((a.comp b).ofNatIsoRight ρ).leftAdjointUniq c) =
        Adjunction.leftAdjointCompIso (a.whiskerRight ℕᵒᵖ) (b.whiskerRight ℕᵒᵖ)
          (c.whiskerRight ℕᵒᵖ)
          (towerScalarRestrictionCompositionOrdinary l E F i L j W) := by
    rw [normalizedComparison_eq]
    exact whisker_associator a b c ρ
  change (Functor.mapDerivedCategoryCompIso (tensor l E F i W)
      (tensor l F L j W)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
        (((a.comp b).ofNatIsoRight ρ).leftAdjointUniq c)) = _
  rw [hordinary]
  have hs (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
      (k : A →ₐ[ℚ_[l]] B) :
      scalarAdj l A B k W =
        Adjunction.mapExactDerivedCategory
          ((pbcScalarAdjunction (constantMap l A B k W)).whiskerRight ℕᵒᵖ) := by
    have := (tensor_exact l A B k W).1
    have := (tensor_exact l A B k W).2
    exact exactAdjunction_eq _
  rw [hs E F i, hs F L j, hs E L (j.comp i)]
  exact (AlgebraicGeometry.ProEtale.AmbientClopen.exact_open_comp_localized
    (a.whiskerRight ℕᵒᵖ) (b.whiskerRight ℕᵒᵖ) (c.whiskerRight ℕᵒᵖ)
    (towerScalarRestrictionCompositionOrdinary l E F i L j W)).symm

end WeilConjectures.PurStrictScalar
