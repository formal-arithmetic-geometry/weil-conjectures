/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The normalized Roos and intrinsic Koszul units agree

Source: Stacks Project, Tags 099M and 0941; Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-a1-roos-intrinsic-unit-comparison).
The maps are specified on chain coordinates, including the zero shifted components.
A total derived limit is evaluated on any K-injective strict-tower resolution; its
comparison is normalized by the actual ordinary-limit inclusion, not just its projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace WeilConjectures.RoosIntrinsicUnitComparison
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})

/-- The actual strict quotient tensor tower, assembled in the tower category.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
abbrev quotientTower (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (targetTower l E W P)

/-- The strict comparison induced by the quotient augmentations, before localization.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
abbrev towerMap (P : CochainComplex (Modules l E W) ℤ) :
    tower l E W P ⟶ quotientTower l E W P :=
  koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W) (comparison l E W P)

/-- The independent quotient unit, obtained by tensoring the specified limit projection.
Source: Stacks 099M (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
def quotientUnit (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    P ⟶ (targetTower l E W P).obj (op n) :=
  (tensorUnit l E W P).inv ≫ (tensorWith l E W P).map
    ((CochainComplex.singleFunctor (Modules l E W) 0).map (projection l E W n))

/-- Zero shifted coordinate and the given product of strict augmentation maps.
Source: Stacks 0941 (blueprint: lem-a1-roos-intrinsic-unit-comparison). -/
def AugmentationFormula (P : CochainComplex (Modules l E W) ℤ)
    (X : CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ)
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)) (η : P ⟶ roosF.obj X) : Prop :=
  ∀ q : ℤ, η.f (q + 1) ≫ (roosχ X q).hom = biprod.lift 0 ((Pi.lift γ).f (q + 1))

section Helpers
attribute [local instance 3000] integralCompletedRingHasDerivedCategory
  integralOperationsCountableProducts
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory IntegralOnSlice.hasDerived
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
  IntegralOnSlice.Site IntegralOnSlice.siteCategory IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.Good
  IntegralOnSlice.qGood IntegralOnSlice.roosGood
  integralOperationsGoodComplex integralOperationsRoosFunctor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible]
  completedIntegralCoefficientSheafUnrestricted
  SheafOfModules.unit SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction HasDerivedCategory.standard

attribute [local implicit_reducible] SheafOfModules.instAbelian
  abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso

private abbrev ComparisonModules := Modules l E W

private def signedFiberIso
    {B : Type*} [Category* B] [Abelian B] {K L : CochainComplex B ℤ}
    (f : K ⟶ L) : CochainComplex.mappingCocone (-f) ≅
      CochainComplex.mappingCocone f := by
  let e : CochainComplex.mappingCone (-f) ≅ CochainComplex.mappingCone f :=
    { hom := CochainComplex.mappingCone.map (-f) f (𝟙 _) (-𝟙 _) (by simp)
      inv := CochainComplex.mappingCone.map f (-f) (𝟙 _) (-𝟙 _) (by simp)
      hom_inv_id := by
        rw [← CochainComplex.mappingCone.map_comp]
        simp only [Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
        exact CochainComplex.mappingCone.map_id _
      inv_hom_id := by
        rw [← CochainComplex.mappingCone.map_comp]
        simp only [Category.id_comp, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
        exact CochainComplex.mappingCone.map_id _ }
  exact (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso e

private theorem signedFiberIso_lift
    {B : Type*} [Category* B] [Abelian B] {K L M : CochainComplex B ℤ}
    (f : K ⟶ L) (α : M ⟶ K) (h : α ≫ f = 0) :
    CochainComplex.mappingCocone.lift (-f) α 0 (by simp [h]) ≫
        (signedFiberIso f).hom =
      CochainComplex.mappingCocone.lift f α 0 (by simp [h]) := by
  simpa only [signedFiberIso, Functor.mapIso_hom, Category.id_comp, Category.comp_id] using
    (completedCoconeLift_natural B (-f) f (𝟙 K) (-𝟙 L) (by simp)
      (𝟙 M) α α (by simp [h]) h (by simp)).symm

private theorem roosAugment_natural
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y)
    {P P' : CochainComplex B ℤ} (g : P ⟶ P')
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (δ : ∀ n : ℕ, P' ⟶ Y.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n)
    (hδ : ∀ n, δ (n + 1) ≫ Y.asFunctor.map (homOfLE n.le_succ).op = δ n)
    (h : ∀ n, g ≫ δ n = γ n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) :
    g ≫ roosAugment δ hδ = roosAugment γ hγ ≫ roosF.map f := by
  apply HomologicalComplex.hom_ext
  intro k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change (g ≫ roosAugment δ hδ).f (p + 1) =
    (roosAugment γ hγ ≫ roosF.map f).f (p + 1)
  apply (cancel_mono (roosχ Y p).hom).1
  simp only [HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [roosF_map_χ, roosAugment_χ]
  rw [← Category.assoc, roosAugment_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simpa only [Category.assoc, roosPmap, Pi.map_π, Pi.lift_π_assoc, Pi.lift_π] using h n

private theorem roosAugment_condition
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n) :
    Pi.lift γ ≫ roosU X = 0 := by
  apply Pi.hom_ext
  intro n
  simp [roosU, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hγ]

private def negativeRoosAugment
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n) :
    P ⟶ CochainComplex.mappingCocone (-roosU X) :=
  CochainComplex.mappingCocone.lift (-roosU X) (Pi.lift γ) 0
    (by simp [roosAugment_condition γ hγ])

section
attribute [local implicit_reducible] ComplexShape.up ComplexShape.up'
  CochainComplex.mappingCone
private theorem negativeRoosAugment_signed
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n) :
    negativeRoosAugment γ hγ ≫ (signedFiberIso (roosU X)).hom = roosAugment γ hγ := by
  exact signedFiberIso_lift (roosU X) (Pi.lift γ) (roosAugment_condition γ hγ)

private theorem negativeRoosAugment_formula
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n) :
    negativeRoosAugment γ hγ ≫ CochainComplex.mappingCocone.fst (-roosU X) =
        Pi.lift γ ∧
      ∀ q : ℤ, (negativeRoosAugment γ hγ).f (q + 1) ≫
        (CochainComplex.mappingCocone.snd (-roosU X)).v
          (q + 1) q (add_neg_cancel_right q 1) = 0 := by
  constructor
  · exact CochainComplex.mappingCocone.lift_fst _ _ _ _
  · intro q
    exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ _ _ _

private theorem signedFiberIso_coordinates
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (q : ℤ) :
    (signedFiberIso (roosU X)).hom.f (q + 1) ≫
        (roosχ X q).hom =
      biprod.lift
        (-(CochainComplex.mappingCocone.snd (-roosU X)).v
          (q + 1) q (add_neg_cancel_right q 1))
        ((CochainComplex.mappingCocone.fst (-roosU X)).f (q + 1)) := by
  let χ := (CochainComplex.mappingCone (-roosU X)).shiftFunctorObjXIso
      (-1) (q + 1) q (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) q (q + 1) rfl ≪≫
      biprod.braiding _ _
  have he : (signedFiberIso (roosU X)).hom.f (q + 1) ≫ (roosχ X q).hom =
      χ.hom ≫ biprod.map (-𝟙 _) (𝟙 _) := by
    dsimp only [signedFiberIso, Functor.mapIso_hom, roosχ, χ, Iso.trans_hom]
    rw [CochainComplex.shiftFunctor_map_f']
    simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso]
    rw [← Category.assoc, ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality]
    simp only [Category.assoc]
    congr 1
    apply CochainComplex.mappingCone.ext_from (-roosU X) (q + 1) q rfl
    · change (CochainComplex.mappingCone.inl (-roosU X)).v (q + 1) q (by omega) ≫
          (CochainComplex.mappingCone.map (-roosU X) (roosU X)
            (𝟙 _) (-𝟙 _) (by simp)).f q ≫ _ = _
      simp only [CochainComplex.mappingCone.map,
        CochainComplex.mappingCone.inl_v_desc_f_assoc,
        CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
      simp only [CochainComplex.mappingCone.inl,
        CochainComplex.HomComplex.Cochain.mk_v, Category.assoc,
        HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
      apply biprod.hom_ext <;> simp
    · rw [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_f_desc_f_assoc]
      simp only [HomologicalComplex.comp_f, CochainComplex.mappingCone.inr, Category.assoc]
      apply biprod.hom_ext <;> simp
  rw [he]
  apply biprod.hom_ext
  · suffices hp :
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (-roosU X) q (q + 1) rfl).hom ≫
            biprod.snd = HomologicalComplex.homotopyCofiber.sndX (-roosU X) q by
      simpa [χ, CochainComplex.mappingCocone.snd,
        CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.snd,
        Category.assoc, Int.negOnePow_even 2 ⟨1, rfl⟩] using
        congrArg (fun f ↦ ((CochainComplex.mappingCone (-roosU X)).shiftFunctorObjXIso
          (-1) (q + 1) q (by omega)).hom ≫ f) hp
    apply CochainComplex.mappingCone.ext_from (-roosU X) (q + 1) q rfl
    · simp [CochainComplex.mappingCone.inl,
        HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    · simp [CochainComplex.mappingCone.inr,
        HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]
  · simp [χ, CochainComplex.mappingCocone.fst,
      CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.fst,
      CochainComplex.HomComplex.Cocycle.homOf, Category.assoc,
      HomologicalComplex.homotopyCofiber.fstX]

end

private theorem transport_unit
    {D : Type*} [Category* D] {X F I U : D}
    (e : F ≅ U) (c : I ≅ U) (ι : X ⟶ I) (υ : X ⟶ U) (α : X ⟶ F)
    (hι : ι ≫ c.hom = υ) (hα : α ≫ e.hom = υ) :
    α ≫ (e ≪≫ c.symm).hom = ι := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc]
  exact c.comp_inv_eq.mpr (hα.trans hι.symm)

private theorem iso_inverse_square
    {D : Type*} [Category* D] {X Y X' Y' : D}
    (a : X ≅ Y) (a' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ a'.hom = a.hom ≫ g) : a.inv ≫ f = g ≫ a'.inv := by
  apply a.inv_comp_eq.mpr
  rw [← Category.assoc]
  exact a'.eq_comp_inv.mpr h

private theorem inverse_comparison_naturality
    {D : Type*} [Category* D] {F F' V V' U U' : D}
    (e : V ≅ U) (e' : V' ≅ U') (c : F ⟶ U) (c' : F' ⟶ U')
    (f : F ⟶ F') (v : V ⟶ V') (u : U ⟶ U')
    (hc : f ≫ c' = c ≫ u) (he : v ≫ e'.hom = e.hom ≫ u) :
    f ≫ (c' ≫ e'.inv) = (c ≫ e.inv) ≫ v := by
  have hi := iso_inverse_square e e' v u he
  calc
    f ≫ (c' ≫ e'.inv) = (f ≫ c') ≫ e'.inv := (Category.assoc _ _ _).symm
    _ = (c ≫ u) ≫ e'.inv := congrArg (fun z ↦ z ≫ e'.inv) hc
    _ = (c ≫ e.inv) ≫ v := by rw [Category.assoc, ← hi, ← Category.assoc]

private theorem unit_compatible_of_comparison
    {B : Type*} [Category* B] {P X X' Y Y' : B}
    (u : P ⟶ X) (u' : P ⟶ X') (v : P ⟶ Y) (v' : P ⟶ Y')
    (a : X ⟶ Y) (a' : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ a = v) (h' : u' ≫ a' = v')
    (hn : f ≫ a' = a ≫ g) (hu : u ≫ f = u') : v ≫ g = v' := by
  calc
    v ≫ g = (u ≫ a) ≫ g := congrArg (fun z ↦ z ≫ g) h.symm
    _ = (u ≫ f) ≫ a' := by rw [Category.assoc, ← hn, ← Category.assoc]
    _ = v' := (congrArg (fun z ↦ z ≫ a') hu).trans h'

private theorem post_mapIso_naturality
    {D B : Type*} [Category* D] [Category* B] (F : D ⥤ B)
    {X X' : B} {Y Y' Z Z' : D}
    (a : X ≅ F.obj Y) (a' : X' ≅ F.obj Y') (e : Y ≅ Z) (e' : Y' ≅ Z')
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (ha : f ≫ a'.hom = a.hom ≫ F.map g) (he : g ≫ e'.hom = e.hom ≫ h) :
    f ≫ (a' ≪≫ F.mapIso e').hom = (a ≪≫ F.mapIso e).hom ≫ F.map h := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ha, Category.assoc, ← F.map_comp, he, F.map_comp,
    ← Category.assoc]

section ConcreteInstances
set_option backward.isDefEq.respectTransparency true
variable [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

section UnitCompatibility
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] tensorUnit tensorWith
attribute [local implicit_reducible] sourceTower targetTower comparison levelUnit quotientUnit
  koszulTowerComplex koszulTowerComplexMap principalKoszulTower principalKoszul
  Functor.ofOpSequence Functor.ofSequence

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem levelUnit_compatible (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    levelUnit l E W P (n + 1) ≫
        (tower l E W P).asFunctor.map (homOfLE n.le_succ).op = levelUnit l E W P n := by
  dsimp only [levelUnit]
  change ((tensorUnit l E W P).inv ≫ (tensorWith l E W P).map _) ≫
    (tensorWith l E W P).map _ = _
  erw [Category.assoc, ← Functor.map_comp]
  apply congrArg ((tensorUnit l E W P).inv ≫ ·)
  apply congrArg (tensorWith l E W P).map
  dsimp only [principalKoszulTower]
  erw [Functor.ofOpSequence_map_homOfLE_succ]
  dsimp only [principalKoszulTransition, CochainComplex.mappingCone.map]
  erw [CochainComplex.mappingCone.inr_desc]
  exact Category.id_comp _

omit [EssentiallySmall.{max u (t + 1)} W.ProEt] in
private theorem levelUnit_comparison (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    levelUnit l E W P n ≫ (comparison l E W P).app (op n) =
      quotientUnit l E W P n := by
  change ((tensorUnit l E W P).inv ≫ (tensorWith l E W P).map _) ≫
    (tensorWith l E W P).map _ = _
  dsimp only [quotientUnit]
  erw [Category.assoc, ← Functor.map_comp]
  apply congrArg ((tensorUnit l E W P).inv ≫ ·)
  apply congrArg (tensorWith l E W P).map
  let F := CochainComplex.singleFunctor (Modules l E W) 0
  let a := multiplication l E W n
  let S : ShortComplex (CochainComplex (Modules l E W) ℤ) :=
    ShortComplex.mk (F.map a) (F.map (cokernel.π a)) (by
      erw [← F.map_comp, cokernel.condition, F.map_zero])
  have h := CochainComplex.mappingCone.inr_descShortComplex S
  change CochainComplex.mappingCone.inr (F.map a) ≫
    (CochainComplex.mappingCone.descShortComplex S ≫ F.map (quotientComparison l E W n)) = _
  erw [← Category.assoc, h, ← F.map_comp]
  dsimp only [quotientComparison]
  erw [cokernel.π_desc]

omit [EssentiallySmall.{max u (t + 1)} W.ProEt] in
private theorem quotientUnit_compatible (P : CochainComplex (Modules l E W) ℤ) (n : ℕ) :
    quotientUnit l E W P (n + 1) ≫
        (quotientTower l E W P).asFunctor.map (homOfLE n.le_succ).op =
      quotientUnit l E W P n := by
  exact unit_compatible_of_comparison
    (levelUnit l E W P (n + 1)) (levelUnit l E W P n)
    (quotientUnit l E W P (n + 1)) (quotientUnit l E W P n)
    ((comparison l E W P).app (op (n + 1))) ((comparison l E W P).app (op n))
    ((sourceTower l E W P).map (homOfLE n.le_succ).op)
    ((targetTower l E W P).map (homOfLE n.le_succ).op)
    (levelUnit_comparison l E W P (n + 1)) (levelUnit_comparison l E W P n)
    ((comparison l E W P).naturality (homOfLE n.le_succ).op)
    (levelUnit_compatible l E W P n)

end UnitCompatibility

omit [EssentiallySmall.{max u (t + 1)} W.ProEt] in
private theorem towerMap_quasiIso
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    QuasiIso (towerMap l E W P.obj) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation
    (V := ComparisonModules l E W) (T := ℕᵒᵖ) (towerMap l E W P.obj)).2
  intro n
  exact (principal_koszul_strict_replacement l E W P.obj P.property.1 P.property.2 n.unop).1

section RoosTowerComparisonAPI
attribute [local irreducible] roosF DerivedCategory DerivedCategory.Q

omit [EssentiallySmall.{max u (t + 1)} W.ProEt] in
private theorem roosTowerMap_isIso
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    IsIso (DerivedCategory.Q.map (roosF.map (towerMap l E W P.obj))) := by
  have := towerMap_quasiIso l E W P
  have : HasExactLimitsOfShape (Discrete ℕ) (Modules l E W) :=
    AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} W
      (completedIntegralCoefficientSheafUnrestricted l E W) ℕ
  have := CategoryTheory.roos_map_quasiIso (A := Modules l E W) (towerMap l E W P.obj)
  infer_instance

end RoosTowerComparisonAPI

private abbrev intrinsicTowerMap
    {P P' : CochainComplex (ComparisonModules l E W) ℤ} (f : P ⟶ P') :
    tower l E W P ⟶ tower l E W P' :=
  koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W)
    (sourceTowerMap l E W f)

private abbrev quotientTowerMap
    {P P' : CochainComplex (ComparisonModules l E W) ℤ} (f : P ⟶ P') :
    @Quiver.Hom (CochainComplex (ℕᵒᵖ ⥤ ComparisonModules l E W) ℤ) inferInstance
      (quotientTower l E W P) (quotientTower l E W P') :=
  koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W)
    (targetTowerMap l E W f)

private def quotientAugmentation (P : CochainComplex (Modules l E W) ℤ) :
    P ⟶ roosF.obj (quotientTower l E W P) :=
  roosAugment (quotientUnit l E W P) (quotientUnit_compatible l E W P)

section
set_option backward.isDefEq.respectTransparency false
variable {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
attribute [local implicit_reducible]
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local implicit_reducible] integralOperationsTowerStep integralOperationsRoos

private theorem roosMap_eq {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) :
    roosF.map f = integralOperationsRoosMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) := by
  unfold integralOperationsRoosMap
  rw [arrowConeMap B _ _ _ _ (integralOperationsRoos_square
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f))]
  rfl

private theorem roosAugment_map {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ}
    {C : ℕᵒᵖ ⥤ CochainComplex B ℤ} (a : X.asFunctor ⟶ C)
    {P : CochainComplex B ℤ} (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n)
    (δ : ∀ n : ℕ, P ⟶ C.obj (op n))
    (hδ : Pi.lift δ ≫ towerTransitionEndomorphism
      (integralOperationsTowerStep C) = 0)
    (ha : ∀ n, γ n ≫ a.app (op n) = δ n) :
    roosAugment γ hγ ≫ integralOperationsRoosMap a =
      CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (integralOperationsTowerStep C))
        (Pi.lift δ) 0 (by simp [hδ]) := by
  have hγ' : Pi.lift γ ≫ roosU X = 0 := by
    apply Pi.hom_ext
    intro n
    simp [towerTransitionEndomorphism, towerProductShift, Category.assoc, hγ]
  unfold integralOperationsRoosMap
  rw [arrowConeMap B _ _ _ _ (integralOperationsRoos_square a)]
  symm
  convert completedCoconeLift_natural B (roosU X) _ _ _
    (integralOperationsRoos_square a) (𝟙 P) _ _ hγ' hδ (by
      apply Pi.hom_ext
      intro n
      simpa only [Category.id_comp, Category.assoc, Pi.map_π, Pi.lift_π,
        Pi.lift_π_assoc] using (ha n).symm) using 1 <;>
    first | rfl | simp only [Category.id_comp]

section RingedRoos
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasCountableProducts (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

private def assembledRoosIso
    (X : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    roosF.obj (koszulTowerComplex R X) ≅ integralOperationsRoos X := Iso.refl _

private theorem assembledRoosIso_natural
    {X Y : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} (a : X ⟶ Y) :
    roosF.map (koszulTowerComplexMap R a) ≫ (assembledRoosIso R Y).hom =
      (assembledRoosIso R X).hom ≫ integralOperationsRoosMap a := by
  simp only [assembledRoosIso, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rw [roosMap_eq]
  rfl

private theorem assembledRoosIso_augment
    (X Y : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (a : X ⟶ Y)
    {P : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.map (homOfLE n.le_succ).op = γ n)
    (δ : ∀ n : ℕ, P ⟶ Y.obj (op n))
    (hδ : Pi.lift δ ≫ towerTransitionEndomorphism (integralOperationsTowerStep Y) = 0)
    (ha : ∀ n, γ n ≫ a.app (op n) = δ n) :
    roosAugment (X := koszulTowerComplex R X) γ hγ ≫
        (assembledRoosIso R X).hom ≫ integralOperationsRoosMap a =
      CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (integralOperationsTowerStep Y))
        (Pi.lift δ) 0 (by simp [hδ]) := by
  simpa only [assembledRoosIso, Iso.refl_hom, Category.id_comp] using
    roosAugment_map (X := koszulTowerComplex R X) a γ hγ δ hδ ha

end RingedRoos

attribute [local irreducible] assembledRoosIso targetTower
  IntegralOnSlice.tower IntegralOnSlice.augmentation

section OrdinaryWrapperAPI
attribute [local semireducible] targetTower
attribute [local implicit_reducible] targetTower Functor.ofOpSequence Functor.ofSequence
attribute [local irreducible] tensorWith tensorUnit

-- These wrappers keep the module category in their types while using the slice constructions.
private def ordinaryTower : CochainComplex (ComparisonModules l E W) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ) :=
  IntegralOnSlice.tower l E W none

private def ordinaryAugmentation :
    (Functor.const ℕᵒᵖ : CochainComplex (ComparisonModules l E W) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ)) ⟶ ordinaryTower l E W :=
  IntegralOnSlice.augmentation l E W none

private def ordinaryRoosUnit (P : CochainComplex (ComparisonModules l E W) ℤ) :
    P ⟶ integralOperationsRoos ((ordinaryTower l E W).obj P) :=
  IntegralOnSlice.roosUnit l E W none P

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem ordinaryTensorComparison :
    ∃ eT : ∀ P : CochainComplex (ComparisonModules l E W) ℤ,
        targetTower l E W P ≅ (ordinaryTower l E W).obj P,
      (∀ (P : CochainComplex (ComparisonModules l E W) ℤ) (n : ℕ),
        quotientUnit l E W P n ≫ (eT P).hom.app (op n) =
          ((ordinaryAugmentation l E W).app P).app (op n)) ∧
      ∀ (P P' : CochainComplex (ComparisonModules l E W) ℤ) (f : P ⟶ P'),
        targetTowerMap l E W f ≫ (eT P').hom =
          (eT P).hom ≫ (ordinaryTower l E W).map f := by
  let eT := (quotientTensorScalarTowerComparison l E W).choose
  refine ⟨eT, ?_, ?_⟩
  · intro P n
    erw [quotientUnit, Category.assoc]
    exact (quotientTensorScalarTowerComparison l E W).choose_spec.1 P n
  · exact (quotientTensorScalarTowerComparison l E W).choose_spec.2

omit [EssentiallySmall.{max u (t + 1)} W.ProEt] in
private theorem ordinaryRoosUnit_eq
    (P : CochainComplex (ComparisonModules l E W) ℤ)
    (hv : Pi.lift (fun n : ℕ ↦ ((ordinaryAugmentation l E W).app P).app (op n)) ≫
      towerTransitionEndomorphism
        (integralOperationsTowerStep ((ordinaryTower l E W).obj P)) = 0) :
    ordinaryRoosUnit l E W P = CochainComplex.mappingCocone.lift
      (towerTransitionEndomorphism
        (integralOperationsTowerStep ((ordinaryTower l E W).obj P)))
      (Pi.lift (fun n : ℕ ↦ ((ordinaryAugmentation l E W).app P).app (op n)))
      0 (by simp only [CochainComplex.HomComplex.δ_zero, hv,
        CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]) := by
  rfl

end OrdinaryWrapperAPI

section ScalarRoosComparison
set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] roosConeFunctor CochainComplex.mappingCocone
  IntegralOnSlice.roos quotientAugmentation koszulTowerComplex koszulTowerComplexMap
attribute [local irreducible] CochainComplex.mappingCone roosF

private theorem tensorScalarRoosComparison :
    ∃ e : ∀ P : CochainComplex (ComparisonModules l E W) ℤ,
        (roosF (A := ComparisonModules l E W)).obj (quotientTower l E W P) ≅
          (IntegralOnSlice.roos l E W none).obj P,
      (∀ P, quotientAugmentation l E W P ≫ (e P).hom =
        IntegralOnSlice.roosUnit l E W none P) ∧
      ∀ (P P' : CochainComplex (ComparisonModules l E W) ℤ) (f : P ⟶ P'),
        (roosF (A := ComparisonModules l E W)).map (quotientTowerMap l E W f) ≫ (e P').hom =
          (e P).hom ≫ (IntegralOnSlice.roos l E W none).map f := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := IntegralOnSlice.abSheafify.{t, u} W none
  let := IntegralOnSlice.abLocallyBijective.{t, u} W none
  let T : CochainComplex (ComparisonModules l E W) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ) :=
    ordinaryTower l E W
  let α : (Functor.const ℕᵒᵖ : CochainComplex (ComparisonModules l E W) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ)) ⟶ T :=
    ordinaryAugmentation l E W
  let eT : ∀ P : CochainComplex (ComparisonModules l E W) ℤ,
      targetTower l E W P ≅ T.obj P :=
    (ordinaryTensorComparison l E W).choose
  have heT (P : CochainComplex (ComparisonModules l E W) ℤ) (n : ℕ) :
      quotientUnit l E W P n ≫ (eT P).hom.app (op n) = (α.app P).app (op n) :=
    (ordinaryTensorComparison l E W).choose_spec.1 P n
  have hnT (P P' : CochainComplex (ComparisonModules l E W) ℤ) (f : P ⟶ P') :
      targetTowerMap l E W f ≫ (eT P').hom = (eT P).hom ≫ T.map f :=
    (ordinaryTensorComparison l E W).choose_spec.2 P P' f
  let OR : (ℕᵒᵖ ⥤ CochainComplex (ComparisonModules l E W) ℤ) ⥤
      CochainComplex (ComparisonModules l E W) ℤ := integralOperationsRoosFunctor
  let e (P : CochainComplex (ComparisonModules l E W) ℤ) :
      roosF.obj (quotientTower l E W P) ≅ OR.obj (T.obj P) :=
    assembledRoosIso (completedIntegralCommRingSheafUnrestricted l E W)
      (targetTower l E W P) ≪≫ OR.mapIso (eT P)
  refine ⟨e, ?_, ?_⟩
  · intro P
    let δ (n : ℕ) : P ⟶ (T.obj P).obj (op n) := (α.app P).app (op n)
    have hδ (n : ℕ) : δ (n + 1) ≫ (T.obj P).map (homOfLE n.le_succ).op = δ n := by
      simpa only [δ, Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] using
        ((α.app P).naturality (homOfLE n.le_succ).op).symm
    have hv : Pi.lift δ ≫
        towerTransitionEndomorphism (integralOperationsTowerStep (T.obj P)) = 0 := by
      apply Pi.hom_ext
      intro n
      simp [towerTransitionEndomorphism, towerProductShift,
        integralOperationsTowerStep, Category.assoc, hδ]
    let u : P ⟶ OR.obj (T.obj P) := ordinaryRoosUnit l E W P
    have hu : u = CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (integralOperationsTowerStep (T.obj P)))
        (Pi.lift δ) 0 (by simp only [CochainComplex.HomComplex.δ_zero, hv,
        CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]) := ordinaryRoosUnit_eq l E W P hv
    change quotientAugmentation l E W P ≫ (e P).hom = u
    rw [hu]
    simpa only [quotientAugmentation, e, Iso.trans_hom, Functor.mapIso_hom,
      OR, integralOperationsRoosFunctor, Category.assoc] using
      assembledRoosIso_augment (completedIntegralCommRingSheafUnrestricted l E W)
        (targetTower l E W P) (T.obj P) (eT P).hom
        (quotientUnit l E W P) (quotientUnit_compatible l E W P)
        δ hv (heT P)
  · intro P P' f
    exact post_mapIso_naturality OR
      (assembledRoosIso (completedIntegralCommRingSheafUnrestricted l E W)
        (targetTower l E W P))
      (assembledRoosIso (completedIntegralCommRingSheafUnrestricted l E W)
        (targetTower l E W P')) (eT P) (eT P')
      (roosF.map (quotientTowerMap l E W f)) (targetTowerMap l E W f) (T.map f)
      (assembledRoosIso_natural (completedIntegralCommRingSheafUnrestricted l E W)
        (targetTowerMap l E W f)) (hnT P P' f)

end ScalarRoosComparison

private theorem normalizedRoosResolution_generic
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    [HasExactLimitsOfShape (Discrete ℕ) B] [IsGrothendieckAbelian B]
    [HasDerivedCategory B]
    (P : CochainComplex B ℤ) (X I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n)
    (q : X ⟶ I) [QuasiIso q] [I.IsKInjective] :
    ∃ (ρ : DerivedCategory.Q.obj (roosF.obj X) ≅
          DerivedCategory.Q.obj (limit I.asFunctor)) (lam : P ⟶ limit I.asFunctor),
      IsIso (DerivedCategory.Q.map (roosι I)) ∧
      ρ.hom ≫ DerivedCategory.Q.map (roosι I) =
        DerivedCategory.Q.map (roosF.map q) ∧
      (∀ n : ℕ, lam ≫ limit.π I.asFunctor (op n) =
        γ n ≫ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
      DerivedCategory.Q.map (roosAugment γ hγ) ≫ ρ.hom =
        DerivedCategory.Q.map lam := by
  let δ (n : ℕ) := γ n ≫
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)
  have hδ (n : ℕ) : δ (n + 1) ≫ I.asFunctor.map (homOfLE n.le_succ).op = δ n := by
    dsimp only [δ]
    calc
      _ = γ (n + 1) ≫ ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app
        (op (n + 1)) ≫ I.asFunctor.map (homOfLE n.le_succ).op) := Category.assoc _ _ _
      _ = γ (n + 1) ≫ (X.asFunctor.map (homOfLE n.le_succ).op ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) :=
        congrArg (γ (n + 1) ≫ ·)
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).naturality
            (homOfLE n.le_succ).op).symm
      _ = _ := by rw [← Category.assoc, hγ]
  let lam := roosAugmentLimit δ hδ
  have := CategoryTheory.roos_map_quasiIso (A := B) q
  have := CategoryTheory.roos_inclusion_quasiIso (A := B) I
  let ρ := asIso (DerivedCategory.Q.map (roosF.map q)) ≪≫
    (asIso (DerivedCategory.Q.map (roosι I))).symm
  refine ⟨ρ, lam, inferInstance, ?_, ?_, ?_⟩
  · simp [ρ]
  · exact fun n ↦ roosAugmentLimit_π δ hδ n
  · apply (cancel_mono (DerivedCategory.Q.map (roosι I))).1
    simp only [ρ, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Functor.map_comp]
    congr 1
    rw [← roosAugment_eq]
    symm
    simpa only [Category.id_comp] using
      (roosAugment_natural q (𝟙 P) γ δ hγ hδ (fun _ ↦ by simp [δ]))

omit [EssentiallySmall.{max u (t + 1)} W.ProEt] in
private theorem normalizedRoosResolution
    (P : CochainComplex (Modules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ)
    (q : quotientTower l E W P ⟶ I) [QuasiIso q] [I.IsKInjective] :
    ∃ (ρ : DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P)) ≅
          DerivedCategory.Q.obj (limit I.asFunctor)) (lam : P ⟶ limit I.asFunctor),
      IsIso (DerivedCategory.Q.map (roosι I)) ∧
      ρ.hom ≫ DerivedCategory.Q.map (roosι I) =
        DerivedCategory.Q.map (roosF.map q) ∧
      (∀ n : ℕ, lam ≫ limit.π I.asFunctor (op n) =
        quotientUnit l E W P n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
      DerivedCategory.Q.map (quotientAugmentation l E W P) ≫ ρ.hom =
        DerivedCategory.Q.map lam := by
  let : HasExactLimitsOfShape (Discrete ℕ) (Modules l E W) :=
    AlgebraicGeometry.Scheme.ProEt.products_exact.{t, u, 0} W
      (completedIntegralCoefficientSheafUnrestricted l E W) ℕ
  let : IsGrothendieckAbelian.{max u (t + 1)} (Modules l E W) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, max u (t + 1), 0}
      _ (completedIntegralCoefficientSheafUnrestricted l E W)
  exact normalizedRoosResolution_generic P (quotientTower l E W P) I
    (quotientUnit l E W P) (quotientUnit_compatible l E W P) q

end

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem good_representative (K : IntegralOnSlice.D l E W none) :
    ∃ P : (IntegralOnSlice.Good l E W none).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let q := IntegralOnSlice.qGood l E W none
  have : q.IsLocalization ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E W none).ι) := IntegralOnSlice.goodLocalization l E W none
  have := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E W none).ι)
  exact ⟨q.objPreimage K, ⟨q.objObjPreimageIso K⟩⟩

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem localTest_shift
    (K : IntegralOnSlice.D l E W none) (U : W.ProEt)
    (s : ((IntegralOnSlice.ring l E W (some U)).obj ⋙ forget CommRingCat).sections)
    (r : ℤ) (h : IsZero (integralCompletionLocalTest l E W K U s)) :
    IsZero (integralCompletionLocalTest l E W (K⟦r⟧) U s) := by
  let : HasSheafify (IntegralOnSlice.topology W (some U))
      CommRingCat.{max u (t + 1)} :=
    let : EssentiallySmall.{max u (t + 1)} (IntegralOnSlice.Site W (some U)) :=
      essentiallySmallSelf _
    hasSheafifyEssentiallySmallSite _ _
  let O := IntegralOnSlice.rings l E W none
  let := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)} (O.over U))
  let F := SheafOfModules.overFunctor O U
  have : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses O U).1
  have : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses O U).2
  let R := IntegralOnSlice.ring l E W (some U)
  let M := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalizationOfUniverses R s)
  let H := RingedHomUniverses.hom (IntegralOnSlice.topology W (some U)) R M
  let e : ringedSiteDerivedRestrictionOfUniverses O U (K⟦r⟧) ≅
      (ringedSiteDerivedRestrictionOfUniverses O U K)⟦r⟧ :=
    SheafOfModules.overFunctor_derivedRestrictionIso O U (K⟦r⟧) ≪≫
      (F.mapDerivedCategory.commShiftIso r).app K ≪≫
      (shiftFunctor _ r).mapIso
        (SheafOfModules.overFunctor_derivedRestrictionIso O U K).symm
  let ee : integralCompletionLocalTest l E W (K⟦r⟧) U s ≅
      (integralCompletionLocalTest l E W K U s)⟦r⟧ :=
    H.mapIso e ≪≫ (H.commShiftIso r).app _
  exact (Functor.map_isZero (shiftFunctor _ r) h).of_iso ee

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private lemma good_shift (P : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P) (m : ℤ) :
    integralOperationsGoodComplex l E W (P⟦m⟧) := by
  refine ⟨?_, fun i ↦ hP.2 (i + m)⟩
  exact SheafOfModules.KFlatFixedTensor.shift_kFlat
    (completedIntegralCommRingSheafUnrestricted l E W) P hP.1 m



omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem complete_shift (K : IntegralOnSlice.D l E W none)
    (hK : IntegralOnSlice.IsComplete l E W none K) (r : ℤ) :
    IntegralOnSlice.IsComplete l E W none (K⟦r⟧) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hpl : p ≠ l := by omega
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  obtain ⟨P, ⟨e⟩⟩ := good_representative l E W K
  obtain ⟨Pr, ⟨er⟩⟩ := good_representative l E W (K⟦r⟧)
  have h := roosIntrinsicCompletenessEquivalence p l hpl E W d hd K P e
  have hr := roosIntrinsicCompletenessEquivalence p l hpl E W d hd (K⟦r⟧) Pr er
  apply (hr.out 0 1).mpr
  have hk := (h.out 0 1).mp hK
  intro U s hs
  exact localTest_shift l E W K U s r (hk U s hs)

attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit

section QuotientDescentAPI
attribute [local irreducible] roosF DerivedCategory DerivedCategory.Q

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem complete_unit_isIso (K : IntegralOnSlice.D l E W none)
    (hK : IntegralOnSlice.IsComplete l E W none K) :
    IsIso ((IntegralOnSlice.completionUnit l E W none).app K) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hpl : p ≠ l := by omega
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  obtain ⟨P, ⟨e⟩⟩ := good_representative l E W K
  exact ((roosIntrinsicCompletenessEquivalence p l hpl E W d hd K P e).out 0 4).mp hK

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem ordinary_completionUnit_comparison
    (P : (IntegralOnSlice.Good l E W none).FullSubcategory) :
    (IntegralOnSlice.completionUnit l E W none).app (DerivedCategory.Q.obj P.obj) ≫
        ((IntegralOnSlice.completionComparison l E W none).app P).hom =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E W none P.obj) := by
  simpa only [IntegralOnSlice.completionUnit, IntegralOnSlice.qGood,
    Functor.comp_obj, ObjectProperty.ι_obj, Iso.app_hom] using
    (IntegralOnSlice.completionUnit_existsUnique l E W none).exists.choose_spec P

private theorem quotientDescent :
    ∃ (FU : DerivedCategory (Modules l E W) ⥤ DerivedCategory (Modules l E W))
      (comp : 𝟭 (DerivedCategory (Modules l E W)) ⟶ FU),
      ∃ eU : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        FU.obj (DerivedCategory.Q.obj P.obj) ≅
          DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P.obj)),
      (∀ P, comp.app
          (DerivedCategory.Q.obj P.obj) ≫ (eU P).hom =
        DerivedCategory.Q.map (quotientAugmentation l E W P.obj)) ∧
      (∀ (P P' : (integralOperationsGoodComplex l E W).FullSubcategory)
        (f : P.obj ⟶ P'.obj),
        FU.map (DerivedCategory.Q.map f) ≫ (eU P').hom =
          (eU P).hom ≫ DerivedCategory.Q.map (roosF.map
            (quotientTowerMap l E W f))) ∧
      ∀ K : DerivedCategory (Modules l E W),
        IntegralOnSlice.IsComplete l E W none K →
          IsIso (comp.app K) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := IntegralOnSlice.abSheafify.{t, u} W none
  let := IntegralOnSlice.abLocallyBijective.{t, u} W none
  let Q : CochainComplex (ComparisonModules l E W) ℤ ⥤
      DerivedCategory (ComparisonModules l E W) :=
    DerivedCategory.Q
  let e := (tensorScalarRoosComparison l E W).choose
  have he := (tensorScalarRoosComparison l E W).choose_spec.1
  have hn := (tensorScalarRoosComparison l E W).choose_spec.2
  let eU (P : (integralOperationsGoodComplex l E W).FullSubcategory) :=
    (IntegralOnSlice.completionComparison l E W none).app
        (⟨P.obj, P.property⟩ : (IntegralOnSlice.Good l E W none).FullSubcategory) ≪≫
      (Q.mapIso (e P.obj)).symm
  refine ⟨IntegralOnSlice.completion l E W none,
    IntegralOnSlice.completionUnit l E W none, eU, ?_, ?_, complete_unit_isIso l E W⟩
  · intro P
    exact transport_unit
      ((IntegralOnSlice.completionComparison l E W none).app
        (⟨P.obj, P.property⟩ : (IntegralOnSlice.Good l E W none).FullSubcategory))
      (Q.mapIso (e P.obj)) (Q.map (quotientAugmentation l E W P.obj))
      (Q.map (IntegralOnSlice.roosUnit l E W none P.obj))
      ((IntegralOnSlice.completionUnit l E W none).app (Q.obj P.obj))
      ((Q.map_comp _ _).symm.trans (congrArg (fun a ↦ Q.map a) (he P.obj)))
      (ordinary_completionUnit_comparison l E W
        (⟨P.obj, P.property⟩ : (IntegralOnSlice.Good l E W none).FullSubcategory))
  · intro P P' f
    have hh :
        (IntegralOnSlice.completion l E W none).map (Q.map f) ≫
            ((IntegralOnSlice.completionComparison l E W none).app
              (⟨P'.obj, P'.property⟩ :
                (IntegralOnSlice.Good l E W none).FullSubcategory)).hom =
          ((IntegralOnSlice.completionComparison l E W none).app
            (⟨P.obj, P.property⟩ :
              (IntegralOnSlice.Good l E W none).FullSubcategory)).hom ≫
            Q.map ((IntegralOnSlice.roos l E W none).map f) :=
      (IntegralOnSlice.completionComparison l E W none).hom.naturality
        (ObjectProperty.homMk (P := IntegralOnSlice.Good l E W none)
          (X := ⟨P.obj, P.property⟩) (Y := ⟨P'.obj, P'.property⟩) f)
    have hnQ :
        Q.map ((roosF (A := ComparisonModules l E W)).map
            (quotientTowerMap l E W f)) ≫ (Q.mapIso (e P'.obj)).hom =
          (Q.mapIso (e P.obj)).hom ≫ Q.map ((IntegralOnSlice.roos l E W none).map f) := by
      change Q.map _ ≫ Q.map (e P'.obj).hom = Q.map (e P.obj).hom ≫ Q.map _
      exact (Q.map_comp _ _).symm.trans
        ((congrArg (fun a ↦ Q.map a) (hn P.obj P'.obj f)).trans (Q.map_comp _ _))
    exact inverse_comparison_naturality (Q.mapIso (e P.obj)) (Q.mapIso (e P'.obj))
      ((IntegralOnSlice.completionComparison l E W none).app
        (⟨P.obj, P.property⟩ : (IntegralOnSlice.Good l E W none).FullSubcategory)).hom
      ((IntegralOnSlice.completionComparison l E W none).app
        (⟨P'.obj, P'.property⟩ : (IntegralOnSlice.Good l E W none).FullSubcategory)).hom
      ((IntegralOnSlice.completion l E W none).map (Q.map f))
      (Q.map (roosF.map (quotientTowerMap l E W f)))
      (Q.map ((IntegralOnSlice.roos l E W none).map f)) hh hnQ


end QuotientDescentAPI


private theorem transport_comparison
    {D : Type*} [Category* D] {F I U : D} (e : F ≅ U) (c : I ≅ U) :
    (e ≪≫ c.symm).inv ≫ e.hom = c.hom := by
  simp [Category.assoc]

private theorem transport_post_first
    {D : Type*} [Category* D] {F I V U : D}
    (e : F ≅ U) (j : I ≅ V) (a : V ≅ U) :
    (e ≪≫ (j ≪≫ a).symm).hom ≫ j.hom = e.hom ≫ a.inv := by
  simp [Category.assoc]


private theorem transport_naturality
    {D : Type*} [Category* D] {F F' I I' V V' U U' : D}
    (e : F ≅ U) (e' : F' ≅ U') (j : I ≅ V) (j' : I' ≅ V')
    (a : V ≅ U) (a' : V' ≅ U') (f : F ⟶ F') (i : V ⟶ V') (u : U ⟶ U')
    (hf : f ≫ e'.hom = e.hom ≫ u) (hn : i ≫ a'.hom = a.hom ≫ u) :
    f ≫ (e' ≪≫ (j' ≪≫ a').symm).hom ≫ j'.hom =
      (e ≪≫ (j ≪≫ a).symm).hom ≫ j.hom ≫ i := by
  have hni := iso_inverse_square a a' i u hn
  have he := transport_post_first e j a
  have he' := transport_post_first e' j' a'
  simpa only [Category.assoc] using
    calc
      f ≫ ((e' ≪≫ (j' ≪≫ a').symm).hom ≫ j'.hom) =
          f ≫ (e'.hom ≫ a'.inv) := by rw [he']
      _ = (e.hom ≫ u) ≫ a'.inv := by rw [← Category.assoc, hf]
      _ = e.hom ≫ (a.inv ≫ i) := by rw [Category.assoc, ← hni]
      _ = ((e ≪≫ (j ≪≫ a).symm).hom ≫ j.hom) ≫ i := by rw [he, Category.assoc]

private theorem unit_isIso_of_iso
    {D : Type*} [Category* D] (F : D ⥤ D) (unit : 𝟭 D ⟶ F)
    {X K : D} (e : X ≅ K) [IsIso (unit.app K)] : IsIso (unit.app X) := by
  have hn : unit.app X ≫ F.map e.hom = e.hom ≫ unit.app K :=
    (unit.naturality e.hom).symm
  have : IsIso (unit.app X ≫ F.map e.hom) := by rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map e.hom)

private theorem normalized_unit_isIso
    {D : Type*} [Category* D] {X F U : D}
    (unit : X ⟶ F) (e : F ≅ U) (η : X ⟶ U) (h : unit ≫ e.hom = η)
    [IsIso unit] : IsIso η := by
  rw [← h]
  infer_instance

private theorem pre_unit_isIso
    {D : Type*} [Category* D] {X I U : D}
    (a : X ⟶ I) (e : I ≅ U) (b : X ⟶ U) (h : a ≫ e.hom = b)
    [IsIso b] : IsIso a := by
  have : IsIso (a ≫ e.hom) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

/-- Naturality transports a complete unit to every normalized representative. -/
private theorem complete_representatives
    {D : Type*} [Category* D] {G : Type*} (x i u : G → D)
    (F : D ⥤ D) (unit : 𝟭 D ⟶ F)
    (ηI : ∀ P, x P ⟶ i P) (ηU : ∀ P, x P ⟶ u P)
    (eU : ∀ P, F.obj (x P) ≅ u P) (c : ∀ P, i P ≅ u P)
    (hcU : ∀ P, unit.app (x P) ≫ (eU P).hom = ηU P)
    (hC : ∀ P, ηI P ≫ (c P).hom = ηU P)
    (Complete : D → Prop) (hc : ∀ K, Complete K → IsIso (unit.app K)) :
    ∀ K, Complete K → IsIso (unit.app K) ∧
      ∀ P, (x P ≅ K) → IsIso (ηU P) ∧ IsIso (ηI P) := by
  intro K hK
  have hunit : IsIso (unit.app K) := hc K hK
  refine ⟨hunit, ?_⟩
  intro P e
  have : IsIso (unit.app (x P)) := unit_isIso_of_iso F unit e
  have hu : IsIso (ηU P) := normalized_unit_isIso _ (eU P) _ (hcU P)
  exact ⟨hu, pre_unit_isIso _ (c P) _ (hC P)⟩

end ConcreteInstances

private def signedRoosIso
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    CochainComplex.mappingCocone (-roosU X) ≅ roosF.obj X :=
  signedFiberIso (roosU X)

private theorem signedRoosIso_augment
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op = γ n) :
    negativeRoosAugment γ hγ ≫ (signedRoosIso X).hom = roosAugment γ hγ := by
  exact negativeRoosAugment_signed γ hγ

attribute [local implicit_reducible] koszulTowerComplex koszulTowerComplexMap
  roosF roosConeFunctor CochainComplex.mappingCocone fiber quotientAugmentation
attribute [local irreducible] CochainComplex.mappingCone roosχ
attribute [local irreducible] signedFiberIso sourceTower targetTower tensorWith
  sourceTowerMap targetTowerMap comparison levelUnit quotientUnit tensorUnit

attribute [local irreducible] roosF
attribute [local irreducible] roosAugment roosLift negativeRoosAugment limit
  DerivedCategory DerivedCategory.Q

set_option maxHeartbeats 400000 in
-- Checking all strict coordinates and natural comparison squares needs extra heartbeats.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The canonical signed unit comparison, its descent and its completeness consequences.

Source: Stacks 099M, 0941; Bhatt--Scholze, Proposition 3.5.1
(blueprint: lem-a1-roos-intrinsic-unit-comparison).

Proof:
1. PrincipalKoszulStrictReplacement.principal_koszul_strict_replacement identifies the
   actual quotient projection with the Koszul cokernel and makes a levelwise quasi-iso.
   ProEt.countableProducts_exact supplies exact products on every W.
2. In the product fiber coordinates the differential is (dx,(1-s)x-dy). The map
   (x,y) to (-y,x), with inverse (y,x) to (x,-y), commutes with differentials and
   takes the intrinsic (u,0) unit to the strict (0,u) Koszul unit.
3. Tensor the equality epsilon composed with the degree-zero inclusion equals pi_n.
   It gives a_n u_V,n = u_U,n. Both units are strictly compatible with transitions;
   the diagonal strict Roos map therefore takes eta_V to eta_U as chain maps.
4. The strict Roos derivation lemmas localize a and normalize rho on every K-injective tower
   resolution by Q(Roos(q)) Q(roos inclusion)^(-1). The strict augmentation clause
   identifies its composite with eta_U with Q(lambda), where lambda has components
   q_n u_U,n. This fixes the actual comp map, rather than an arbitrary cone lift.
5. The total tensor quotient tower is identified, with its actual unit and naturally
   in P, with ordinary scalar reduction. Transport the existing completionComparison
   through the Roos image of this tower isomorphism. The normalization clause of
   completionUnit_existsUnique identifies its unit with the actual quotient unit.
   Set both descended functors to this completion and use the inverse of Q(j then a)
   to obtain the intrinsic representative comparison and both naturality equations.
6. The existing Roos-intrinsic completeness equivalences identify Roos completeness
   with invertibility of the specified completion unit. Use a good representative,
   then cancel the normalized representative comparisons to prove invertibility of
   the actual quotient and intrinsic units for every representative.
7. The same completeness equivalences characterize completeness by local derived-Hom
   vanishing. Restriction and the right internal-Hom functor commute with shift, so
   these tests still vanish for K[r]. Tensor shift isomorphisms preserve K-flatness,
   and shifted terms are reindexed flat terms. Apply the complete-unit conclusion to
   the shifted good representative and its shifted representation isomorphism.

All indices n represent positive exponent n+1. W may be empty and K may be zero or
unbounded. No boundedness, constructibility, geometric finiteness or relation between
coefficient and scheme universes is assumed. -/
theorem roos_intrinsic_unit_comparison :
    ∃ (ηI : ∀ P : CochainComplex (Modules l E W) ℤ, P ⟶ fiber l E W P)
      (ηV : ∀ P : CochainComplex (Modules l E W) ℤ, P ⟶ roosF.obj (tower l E W P))
      (ηU : ∀ P : CochainComplex (Modules l E W) ℤ, P ⟶ roosF.obj (quotientTower l E W P))
      (j : ∀ P : CochainComplex (Modules l E W) ℤ,
        fiber l E W P ≅ roosF.obj (tower l E W P)),
      (∀ P, UnitFormula l E W P (ηI P)) ∧
      (∀ P, AugmentationFormula l E W P (tower l E W P) (levelUnit l E W P) (ηV P)) ∧
      (∀ P, AugmentationFormula l E W P (quotientTower l E W P)
        (quotientUnit l E W P) (ηU P)) ∧
      (∀ (P : CochainComplex (Modules l E W) ℤ) (q : ℤ),
        (j P).hom.f (q + 1) ≫ (roosχ (tower l E W P) q).hom =
          biprod.lift
            (-(CochainComplex.mappingCocone.snd (-roosU (tower l E W P))).v
              (q + 1) q (add_neg_cancel_right q 1))
            ((CochainComplex.mappingCocone.fst (-roosU (tower l E W P))).f (q + 1))) ∧
      (∀ P, ηI P ≫ (j P).hom = ηV P ∧
        ηV P ≫ roosF.map (towerMap l E W P) = ηU P) ∧
      ∃ (FI FU : DerivedCategory (Modules l E W) ⥤ DerivedCategory (Modules l E W))
        (unitI : 𝟭 (DerivedCategory (Modules l E W)) ⟶ FI)
        (comp : 𝟭 (DerivedCategory (Modules l E W)) ⟶ FU) (d : FI ≅ FU)
        (eI : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
          FI.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj (fiber l E W P.obj))
        (eU : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
          FU.obj (DerivedCategory.Q.obj P.obj) ≅
            DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P.obj))),
        unitI ≫ d.hom = comp ∧
        (∀ P, unitI.app (DerivedCategory.Q.obj P.obj) ≫ (eI P).hom =
          DerivedCategory.Q.map (ηI P.obj)) ∧
        (∀ P, comp.app (DerivedCategory.Q.obj P.obj) ≫ (eU P).hom =
          DerivedCategory.Q.map (ηU P.obj)) ∧
        (∀ P, (eI P).inv ≫ d.hom.app (DerivedCategory.Q.obj P.obj) ≫ (eU P).hom =
          DerivedCategory.Q.map ((j P.obj).hom ≫ roosF.map (towerMap l E W P.obj))) ∧
        (∀ (P P' : (integralOperationsGoodComplex l E W).FullSubcategory)
          (f : P.obj ⟶ P'.obj),
          FU.map (DerivedCategory.Q.map f) ≫ (eU P').hom =
            (eU P).hom ≫ DerivedCategory.Q.map (roosF.map
              (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W)
                (targetTowerMap l E W f)))) ∧
        (∀ (P P' : (integralOperationsGoodComplex l E W).FullSubcategory)
          (f : P.obj ⟶ P'.obj),
          FI.map (DerivedCategory.Q.map f) ≫ (eI P').hom ≫
              DerivedCategory.Q.map (j P'.obj).hom =
            (eI P).hom ≫ DerivedCategory.Q.map (j P.obj).hom ≫
              DerivedCategory.Q.map (roosF.map
                (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W)
                  (sourceTowerMap l E W f)))) ∧
        (∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
          (I : CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ)
          (q : quotientTower l E W P.obj ⟶ I) [QuasiIso q] [I.IsKInjective],
          ∃ (ρ : DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P.obj)) ≅
              DerivedCategory.Q.obj (limit I.asFunctor))
            (lam : P.obj ⟶ limit I.asFunctor),
            IsIso (DerivedCategory.Q.map (roosι I)) ∧
            ρ.hom ≫ DerivedCategory.Q.map (roosι I) =
              DerivedCategory.Q.map (roosF.map q) ∧
            (∀ n : ℕ, lam ≫ limit.π I.asFunctor (op n) =
              quotientUnit l E W P.obj n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
            DerivedCategory.Q.map (ηU P.obj) ≫ ρ.hom = DerivedCategory.Q.map lam ∧
            DerivedCategory.Q.map (ηI P.obj) ≫
                DerivedCategory.Q.map ((j P.obj).hom ≫ roosF.map (towerMap l E W P.obj)) ≫
                  ρ.hom = DerivedCategory.Q.map lam) ∧
        (∀ (K : DerivedCategory (Modules l E W)),
          IntegralOnSlice.IsComplete l E W none K →
            IsIso (unitI.app K) ∧ IsIso (comp.app K) ∧
            (∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
              (_e : DerivedCategory.Q.obj P.obj ≅ K), IsIso (DerivedCategory.Q.map (ηU P.obj)) ∧
                IsIso (DerivedCategory.Q.map (ηI P.obj))) ∧
            ∀ r : ℤ, IntegralOnSlice.IsComplete l E W none (K⟦r⟧) ∧
              IsIso (unitI.app (K⟦r⟧)) ∧ IsIso (comp.app (K⟦r⟧)) ∧
              ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
                (_e : DerivedCategory.Q.obj P.obj ≅ K),
                CochainComplex.IsKFlatIndependentCoefficients
                  (R := completedIntegralCommRingSheafUnrestricted l E W) (P.obj⟦r⟧) ∧
                (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
                  (R := completedIntegralCommRingSheafUnrestricted l E W) ((P.obj⟦r⟧).X i)) ∧
                IsIso (DerivedCategory.Q.map (ηU (P.obj⟦r⟧))) ∧
                IsIso (DerivedCategory.Q.map (ηI (P.obj⟦r⟧)))) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  let := IntegralOnSlice.abSheafify.{t, u} W none
  let := IntegralOnSlice.abLocallyBijective.{t, u} W none
  let FU : DerivedCategory (ComparisonModules l E W) ⥤
      DerivedCategory (ComparisonModules l E W) := (quotientDescent l E W).choose
  let comp : 𝟭 (DerivedCategory (ComparisonModules l E W)) ⟶ FU :=
    (quotientDescent l E W).choose_spec.choose
  let eU : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      FU.obj (DerivedCategory.Q.obj P.obj) ≅
        DerivedCategory.Q.obj (roosF.obj (quotientTower l E W P.obj)) :=
    (quotientDescent l E W).choose_spec.choose_spec.choose
  have hcU (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      comp.app (DerivedCategory.Q.obj P.obj) ≫ (eU P).hom =
        DerivedCategory.Q.map (quotientAugmentation l E W P.obj) :=
    (quotientDescent l E W).choose_spec.choose_spec.choose_spec.1 P
  have hnU (P P' : (integralOperationsGoodComplex l E W).FullSubcategory)
      (f : P.obj ⟶ P'.obj) :
      FU.map (DerivedCategory.Q.map f) ≫ (eU P').hom =
        (eU P).hom ≫ DerivedCategory.Q.map (roosF.map (quotientTowerMap l E W f)) :=
    (quotientDescent l E W).choose_spec.choose_spec.choose_spec.2.1 P P' f
  have hcompComplete (K : DerivedCategory (ComparisonModules l E W))
      (hK : IntegralOnSlice.IsComplete l E W none K) : IsIso (comp.app K) :=
    (quotientDescent l E W).choose_spec.choose_spec.choose_spec.2.2 K hK
  let Q : CochainComplex (ComparisonModules l E W) ℤ ⥤ DerivedCategory (ComparisonModules l E W) :=
    DerivedCategory.Q
  let RF : CochainComplex
      (ℕᵒᵖ ⥤ ComparisonModules l E W) ℤ ⥤
      CochainComplex (ComparisonModules l E W) ℤ := roosF
  classical
  let ηI (P : CochainComplex (ComparisonModules l E W) ℤ) : P ⟶ fiber l E W P :=
    negativeRoosAugment (B := ComparisonModules l E W) (X := tower l E W P)
      (levelUnit l E W P) (levelUnit_compatible l E W P)
  let ηV (P : CochainComplex (ComparisonModules l E W) ℤ) :
      P ⟶ RF.obj (tower l E W P) :=
    roosAugment (A := ComparisonModules l E W) (X := tower l E W P)
      (levelUnit l E W P) (levelUnit_compatible l E W P)
  let ηU (P : CochainComplex (ComparisonModules l E W) ℤ) :
      P ⟶ RF.obj (quotientTower l E W P) := quotientAugmentation l E W P
  let j (P : CochainComplex (ComparisonModules l E W) ℤ) :
      fiber l E W P ≅ RF.obj (tower l E W P) :=
    signedRoosIso (B := ComparisonModules l E W) (tower l E W P)
  have hIV (P : CochainComplex (ComparisonModules l E W) ℤ) : ηI P ≫ (j P).hom = ηV P :=
    signedRoosIso_augment (B := ComparisonModules l E W)
      (X := tower l E W P) (levelUnit l E W P) (levelUnit_compatible l E W P)
  have hVU (P : CochainComplex (ComparisonModules l E W) ℤ) :
      ηV P ≫ RF.map (towerMap l E W P) = ηU P := by
    have hh := roosAugment_natural
      (B := ComparisonModules l E W)
      (X := tower l E W P) (Y := quotientTower l E W P)
      (towerMap l E W P) (𝟙 P)
      (levelUnit l E W P) (quotientUnit l E W P)
      (levelUnit_compatible l E W P) (quotientUnit_compatible l E W P)
      (fun n ↦ (Category.id_comp _).trans (levelUnit_comparison l E W P n).symm)
    exact hh.symm.trans (Category.id_comp _)
  refine ⟨ηI, ηV, ηU, j, ?_, ?_, ?_, ?_, fun P ↦ ⟨hIV P, hVU P⟩, ?_⟩
  · intro P
    exact negativeRoosAugment_formula
      (B := ComparisonModules l E W)
      (X := tower l E W P) (levelUnit l E W P) (levelUnit_compatible l E W P)
  · intro P q
    exact roosAugment_χ (A := ComparisonModules l E W) (X := tower l E W P)
      (levelUnit l E W P) (levelUnit_compatible l E W P) q
  · intro P q
    exact roosAugment_χ (A := ComparisonModules l E W) (X := quotientTower l E W P)
      (quotientUnit l E W P) (quotientUnit_compatible l E W P) q
  · intro P q
    have h := signedFiberIso_coordinates (B := ComparisonModules l E W) (tower l E W P) q
    convert h using 1 <;> rfl
  · have ha (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
        IsIso (Q.map (RF.map (towerMap l E W P.obj))) :=
      roosTowerMap_isIso l E W P
    let aIso (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
        Q.obj (RF.obj (tower l E W P.obj)) ≅
          Q.obj (RF.obj (quotientTower l E W P.obj)) :=
      letI := ha P
      asIso (Q.map (RF.map (towerMap l E W P.obj)))
    let cIso (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
        Q.obj (fiber l E W P.obj) ≅ Q.obj (RF.obj (quotientTower l E W P.obj)) :=
      Q.mapIso (j P.obj) ≪≫ aIso P
    let eI (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
        FU.obj (Q.obj P.obj) ≅ Q.obj (fiber l E W P.obj) :=
      eU P ≪≫ (cIso P).symm
    have hIU (P : CochainComplex (ComparisonModules l E W) ℤ) :
        ηI P ≫ ((j P).hom ≫ RF.map (towerMap l E W P)) = ηU P := by
      rw [← Category.assoc, hIV P, hVU P]
    have hC (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
        Q.map (ηI P.obj) ≫ (cIso P).hom = Q.map (ηU P.obj) := by
      simpa only [cIso, aIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
        Functor.map_comp, Category.assoc] using
        congrArg (fun f ↦ Q.map f) (hIU P.obj)
    refine ⟨FU, FU, comp, comp, Iso.refl _, eI, eU, Category.comp_id comp,
      ?_, hcU, ?_, hnU, ?_, ?_, ?_⟩
    · intro P
      exact transport_unit (eU P) (cIso P) (Q.map (ηI P.obj))
        (Q.map (ηU P.obj)) (comp.app (Q.obj P.obj)) (hC P) (hcU P)
    · intro P
      simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
      change (eU P ≪≫ (cIso P).symm).inv ≫ (eU P).hom = _
      exact (transport_comparison (eU P) (cIso P)).trans
        (Q.map_comp (j P.obj).hom (RF.map (towerMap l E W P.obj))).symm
    · intro P P' f
      have hnat :
          Q.map (RF.map (intrinsicTowerMap l E W f)) ≫ (aIso P').hom =
            (aIso P).hom ≫ Q.map (RF.map (quotientTowerMap l E W f)) := by
        change Q.map (RF.map (intrinsicTowerMap l E W f)) ≫ Q.map (RF.map (towerMap l E W P'.obj)) =
          Q.map (RF.map (towerMap l E W P.obj)) ≫
            Q.map (RF.map (quotientTowerMap l E W f))
        have hs : intrinsicTowerMap l E W f ≫
              towerMap l E W P'.obj =
            towerMap l E W P.obj ≫ quotientTowerMap l E W f := by
          apply HomologicalComplex.hom_ext
          intro i
          apply NatTrans.ext
          funext n
          exact congrArg (fun a ↦ (a.app n).f i) (comparison_naturality l E W f)
        exact ((RF ⋙ Q).map_comp _ _).symm.trans
          ((congrArg (fun a ↦ (RF ⋙ Q).map a) hs).trans ((RF ⋙ Q).map_comp _ _))
      have hnU' : FU.map (Q.map f) ≫ (eU P').hom =
          (eU P).hom ≫ Q.map (RF.map (quotientTowerMap l E W f)) := hnU P P' f
      exact transport_naturality (D := DerivedCategory (ComparisonModules l E W))
        (eU P) (eU P')
        (Q.mapIso (j P.obj)) (Q.mapIso (j P'.obj)) (aIso P) (aIso P')
        (FU.map (Q.map f))
        (Q.map (RF.map (intrinsicTowerMap l E W f)))
        (Q.map (RF.map (quotientTowerMap l E W f))) hnU' hnat
    · intro P I q hq hI
      have hr := normalizedRoosResolution l E W P.obj I q
      let ρ := hr.choose
      let lam := hr.choose_spec.choose
      have hs := hr.choose_spec.choose_spec
      refine ⟨ρ, lam, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
      rw [← Category.assoc, ← Q.map_comp, hIU P.obj]
      exact hs.2.2.2
    · have hcomplete := complete_representatives
        (D := DerivedCategory (ComparisonModules l E W))
        (G := (integralOperationsGoodComplex l E W).FullSubcategory)
        (fun P : (integralOperationsGoodComplex l E W).FullSubcategory ↦ Q.obj P.obj)
        (fun P ↦ Q.obj (fiber l E W P.obj))
        (fun P ↦ Q.obj (RF.obj (quotientTower l E W P.obj))) FU comp
        (fun P ↦ Q.map (ηI P.obj)) (fun P ↦ Q.map (ηU P.obj))
        eU cIso hcU hC (IntegralOnSlice.IsComplete l E W none) hcompComplete
      intro K hK
      obtain ⟨hc, hunits⟩ := hcomplete K hK
      refine ⟨hc, hc, hunits, ?_⟩
      intro r
      have hKr := complete_shift l E W K hK r
      obtain ⟨hcr, hur⟩ := hcomplete (K⟦r⟧) hKr
      refine ⟨hKr, hcr, hcr, ?_⟩
      intro P eP
      have hPr := good_shift l E W P.obj P.property r
      let Pr : (integralOperationsGoodComplex l E W).FullSubcategory := ⟨P.obj⟦r⟧, hPr⟩
      let er : Q.obj Pr.obj ≅ K⟦r⟧ :=
        (Q.commShiftIso r).app P.obj ≪≫ (shiftFunctor _ r).mapIso eP
      obtain ⟨hu, hi⟩ := hur Pr er
      exact ⟨hPr.1, hPr.2, hu, hi⟩

end Helpers

end WeilConjectures.RoosIntrinsicUnitComparison
