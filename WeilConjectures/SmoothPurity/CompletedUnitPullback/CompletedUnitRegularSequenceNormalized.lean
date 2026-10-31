/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientLevelwiseFlatModels
import WeilConjectures.SmoothPurity.StrictQuotient.StrictUnitOrdinaryAdjoint
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
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

/-! # Normalization of the regular coefficient sequence

Source: Bhatt--Scholze Sections 3.5 and 6.5; Stacks 0941.

The regular module in degree zero has scalar-extension-invertible horizontal
transitions. This statement concerns finite horizontal quotients and does not
assert a derived inverse-limit comparison.
(blueprint: lem-pur-completed-unit-regular-sequence-normalized)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open MonoidalCategory StrictQuotient

private theorem transpose_from_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {U : B ⥤ A} (am : E ⊣ U)
    (I : A ⥤ C) (J : B ⥤ D) {F : C ⥤ D} {R : D ⥤ C} (ad : F ⊣ R)
    (ρ : J ⋙ R ≅ U ⋙ I) (P : A) (ε : F.obj (I.obj P) ⟶ J.obj (E.obj P))
    (hu : ad.unit.app (I.obj P) ≫ R.map ε ≫ ρ.hom.app (E.obj P) =
      I.map (am.unit.app P)) (H : B) (g : P ⟶ U.obj H) :
    (ad.homEquiv _ _).symm (I.map g ≫ ρ.inv.app H) =
      ε ≫ J.map ((am.homEquiv _ _).symm g) := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ad.homEquiv_unit, R.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (I.obj P) ≫ R.map ε =
      I.map (am.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact hu.trans (Category.comp_id _).symm
  rw [hu', Category.assoc]
  have hn := ρ.inv.naturality ((am.homEquiv P H).symm g)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← I.map_comp]
  have hg : am.unit.app P ≫ U.map ((am.homEquiv P H).symm g) = g := by
    exact (am.homEquiv_unit P H ((am.homEquiv P H).symm g)).symm.trans
      ((am.homEquiv P H).apply_symm_apply g)
  rw [hg]

private theorem alpha_eq_model {W : Scheme.{u}} (K : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (hK : Good l E K m) :
    alpha l E K S D hmn =
      (coefficientFiniteQuotientModel l E W hmn (level l E K m) hK.1).hom ≫
        DerivedCategory.Q.map (ordinaryAlpha l E K S D hmn) := by
  exact transpose_from_unit
    ((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (D.adjunction hmn)
    (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors
    (level l E K m)
    (coefficientFiniteQuotientModel l E W hmn (level l E K m) hK.1).hom
    (D.unit_model hmn (level l E K m) hK.1) (level l E K n)
    (transition l E K hmn)

private theorem comparison_cancel
    {C : Type*} [Category C] {A B D F : C}
    (a : A ⟶ B) (b : B ⟶ D) (e : F ≅ D) :
    (a ≫ b ≫ e.inv) ≫ e.hom = a ≫ b := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem sequence_transition_fac {W : Scheme.{u}} (K : Complex l E W)
    {m n : ℕ} (hmn : n ≤ m) :
    (coefficientSequenceDerivedTransition l E W hmn).app (DerivedCategory.Q.obj K) ≫
        (normalizedDVRRes l E W hmn).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app K) ≫
        (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.hom.app
          (level l E K n) =
      (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (transition l E K hmn) := by
  unfold coefficientSequenceDerivedTransition
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso]
  exact comparison_cancel
    ((coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app K)
    (DerivedCategory.Q.map (transition l E K hmn))
    ((coefficientSequenceEvaluation l E W n ⋙
      normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.app K)

private theorem conjugate_adjoint
    {B C : Type*} [Category B] [Category C]
    {L : B ⥤ C} {R : C ⥤ B} (aq : L ⊣ R)
    {M M' : B} {N N' : C} (em : M ≅ M') (en : N ≅ N')
    (t : M ⟶ R.obj N) (u : M' ⟶ R.obj N')
    (h : t ≫ R.map en.hom = em.hom ≫ u) :
    (aq.homEquiv _ _).symm t =
      L.map em.hom ≫ (aq.homEquiv _ _).symm u ≫ en.inv := by
  apply (cancel_mono en.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (aq.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

private theorem unit_system_good (W : Scheme.{u}) :
    CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (𝟙_ (Complex l E W)) ∧
      ∀ k : ℤ, SheafOfModules.IsFlatOnSite
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) ((𝟙_ (Complex l E W)).X k) := by
  let R := coefficientSequenceCommRingSheaf l E W
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  constructor
  · intro T hT k
    exact (hT k).of_iso (ρ_ T).symm
  · intro k
    have hf : ObjectProperty.flat ((𝟙_ (Complex l E W)).X k) := by
      by_cases hk : k = 0
      · subst k
        exact (ObjectProperty.flat).prop_of_iso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ _)).symm
          (ObjectProperty.prop_unit _)
      · exact (ObjectProperty.flat).prop_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ _) k hk)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2

private theorem normalized_regular_unit (W : Scheme.{u}) :
    IsNormalizedCoefficientSequence l E W
      (DerivedCategory.Q.obj (𝟙_ (StrictQuotient.Complex l E W))) := by
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  let D := S.quotientCalculus
  intro m n hmn P
  let em := (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.app
    (𝟙_ (StrictQuotient.Complex l E W))
  let en := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app
    (𝟙_ (StrictQuotient.Complex l E W))
  let a := ((D.adjunction hmn).homEquiv _ _).symm
    ((coefficientSequenceDerivedTransition l E W hmn).app
      (DerivedCategory.Q.obj (𝟙_ (StrictQuotient.Complex l E W))))
  have ht := sequence_transition_fac l E
    (𝟙_ (StrictQuotient.Complex l E W)) hmn
  have hα : a =
      (coefficientFiniteQuotientDerived l E W hmn).map em.hom ≫
        StrictQuotient.alpha l E (𝟙_ (StrictQuotient.Complex l E W))
          S.toCoefficientDerivedSystemTensors D hmn ≫ en.inv := by
    have hh :
        (coefficientSequenceDerivedTransition l E W hmn).app
              (DerivedCategory.Q.obj (𝟙_ (StrictQuotient.Complex l E W))) ≫
            (normalizedDVRRes l E W hmn).map en.hom =
          em.hom ≫ (DerivedCategory.Q.map
              (StrictQuotient.transition l E (𝟙_ (StrictQuotient.Complex l E W)) hmn) ≫
            (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.inv.app
              (StrictQuotient.level l E (𝟙_ (StrictQuotient.Complex l E W)) n)) := by
      exact (((normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.app
        (StrictQuotient.level l E (𝟙_ (StrictQuotient.Complex l E W)) n)).eq_comp_inv.mpr
          ((Category.assoc _ _ _).trans ht)).trans (Category.assoc _ _ _)
    exact conjugate_adjoint (D.adjunction hmn) em en
      ((coefficientSequenceDerivedTransition l E W hmn).app
        (DerivedCategory.Q.obj (𝟙_ (StrictQuotient.Complex l E W))))
      (DerivedCategory.Q.map
          (StrictQuotient.transition l E (𝟙_ (StrictQuotient.Complex l E W)) hmn) ≫
        (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.inv.app
          (StrictQuotient.level l E (𝟙_ (StrictQuotient.Complex l E W)) n)) hh
  have hαi : IsIso (StrictQuotient.alpha l E (𝟙_ (StrictQuotient.Complex l E W))
      S.toCoefficientDerivedSystemTensors D hmn) := by
    rw [alpha_eq_model l E (𝟙_ (StrictQuotient.Complex l E W))
      S.toCoefficientDerivedSystemTensors D hmn (by
        exact ((levelwiseFlatModels l E W _).2 (unit_system_good l E W) m))]
    have := StrictQuotient.strictUnitOrdinaryAdjoint l E W
      S.toCoefficientDerivedSystemTensors D hmn
    infer_instance
  have : IsIso a := by rw [hα]; infer_instance
  have hb := ((D.adjunction hmn).homEquiv _ P).bijective.comp
    (Iso.homCongr (asIso a).symm (Iso.refl P)).bijective
  simpa only [Function.comp_def, Iso.homCongr_apply, Iso.symm_inv, asIso_hom,
    Iso.refl_hom, Category.comp_id, Adjunction.homEquiv_naturality_right,
    a, Equiv.apply_symm_apply] using hb

/-- The regular quotient sequence is normalized for every horizontal quotient map.

Source: Zheng Construction 4.1; Stacks 0941, and the regular-module computation in
Bhatt--Scholze Section 6.5.
Proof: evaluate the degree-zero regular sequence at m and n using the sectionwise
identity identifications b. The actual horizontal transition is the quotient ring
map on sections. Its scalar-extension adjunct is ordinary multiplication, with
inverse z to 1 tensor z. The regular module is flat, so its single complex is
K-flat and ordinary scalar extension computes derived scalar extension. Transport
the multiplication isomorphism through the specified derived adjunction. Its Hom
bijection is exactly the transition-precomposition map in the definition of
IsNormalizedCoefficientSequence. This works for n=m, zero rings on empty objects,
and the empty scheme, without an invertibility assumption on W.
(blueprint: lem-pur-completed-unit-regular-sequence-normalized). -/
theorem regularSequenceNormalized (W : Scheme.{u})
    (b : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n))
    (hb : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
      (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V),
      HEq ((b n).hom.val.app V x) x) :
    IsNormalizedCoefficientSequence l E W (systemObject l E W) := by
  exact (fun _ ↦ normalized_regular_unit l E W) hb

end WeilConjectures.CompletedUnitPullback
