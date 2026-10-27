/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Sheaf.CategoryTheory.DerivedCategory.SmallPerfectCoefficientLift
import Sheaf.Algebra.Homology.PerfectDualScalarCalculus
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Sheaf.Paper.SectionsRationalModelComparison
import Sheaf.Paper.IntegralSectionsPerfectReduction
import Mathlib.RingTheory.TensorProduct.Finite
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Perfect models and descent of field-valued cohomology

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
thm-pod-point-perfectness.proof.md, Step 3
(blueprint: lem-sf-field-cohomology-perfect-descent).

The integral models use small coefficient modules. Their canonical carrier and
coefficient lifts compare them with the published integral sections complexes.
The signed dual is the existing moduleHomComplex into the tensor unit E[0].
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 10000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The canonical lift of an integral model, changing only carrier and coefficient size.
Source: blueprint Step 3, integral model convention
(blueprint: lem-sf-field-cohomology-perfect-descent). -/
abbrev fieldCohomologyIntegralModelLift (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) ℤ :=
  (ModuleCat.uliftFunctor.{u + 1, u} R ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom).mapHomologicalComplex (.up ℤ)

private theorem perfect_pointFiniteDimensional {F : Type u} [Field F]
    {C : DerivedCategory.{u} (ModuleCat.{u} F)} (hC : C.IsPerfect) :
    DerivedCategory.pointFiniteDimensional F C := by
  classical
  obtain ⟨a, b, ha, hb⟩ := hC.exists_homologyConcentratedIn
  refine ⟨⟨Finset.Icc a b, fun i hi ↦ ?_⟩, hC.finite_homology⟩
  have hi' : i < a ∨ b < i := by simpa only [Finset.mem_Icc, not_and_or,
    not_le] using hi
  rcases hi' with hi | hi
  · exact C.isZero_of_isGE a i hi
  · exact C.isZero_of_isLE b i hi

private theorem projective_model_dual {F : Type u} [Field F]
    (P : CochainComplex (ModuleCat.{u} F) ℤ) (b : ℤ) (hb : P.IsStrictlyLE b)
    (C : DerivedCategory.{u} (ModuleCat.{u} F)) (e : C ≅ DerivedCategory.Q.obj P) :
    Nonempty ((ihom C).obj (𝟙_ _) ≅ DerivedCategory.Q.obj
      (CochainComplex.moduleHomComplex P (𝟙_ _))) := by
  obtain ⟨H, ev, _, _, eHom, _, _⟩ := CochainComplex.projective_hom_evaluation_model F
  let eUnit : 𝟙_ (DerivedCategory (ModuleCat.{u} F)) ≅
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} F) ℤ)) :=
    (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app _
  let ePre : (ihom (DerivedCategory.Q.obj P)).obj (𝟙_ _) ≅
      (ihom C).obj (𝟙_ _) := asIso ((MonoidalClosed.pre e.hom).app (𝟙_ _))
  exact ⟨ePre.symm ≪≫ (ihom (DerivedCategory.Q.obj P)).mapIso eUnit ≪≫
    (eHom P ⟨b, fun i hi ↦ P.isZero_of_isStrictlyLE b i hi⟩
      (fun i ↦ inferInstance) (𝟙_ _)).symm⟩

private theorem pointFiniteDimensional_perfect {F : Type u} [Field F]
    {C : DerivedCategory.{u} (ModuleCat.{u} F)}
    (hC : DerivedCategory.pointFiniteDimensional F C) : C.IsPerfect := by
  obtain ⟨s, hs⟩ := hC.1
  obtain ⟨a, ha⟩ := s.bddBelow
  obtain ⟨b, hb⟩ := s.bddAbove
  apply (DerivedCategory.isPerfect_iff C).2
  refine ⟨⟨a, b, ?_, ?_⟩, hC.2⟩
  · rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hs i (fun h ↦ (not_le.mpr hi) (ha h))
  · rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hs i (fun h ↦ (not_le.mpr hi) (hb h))

private theorem signed_dual_bounds {F : Type u} [Field F]
    (P : CochainComplex (ModuleCat.{u} F) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    (CochainComplex.moduleHomComplex P (𝟙_ _)).IsStrictlyGE (-b) ∧
      (CochainComplex.moduleHomComplex P (𝟙_ _)).IsStrictlyLE (-a) := by
  have hz (j : ℤ) (h : IsZero (P.X (-j))) :
      IsZero ((CochainComplex.moduleHomComplex P (𝟙_ _)).X j) := by
    apply ModuleCat.isZero_iff_subsingleton.2
    refine ⟨fun z w ↦ ?_⟩
    apply (CochainComplex.HomComplex.Cochain.toSingleEquiv (K := P)
      (X := ModuleCat.of F F) (show -j + j = 0 by omega)).injective
    exact h.eq_of_src _ _
  constructor
  · apply ((CochainComplex.moduleHomComplex P (𝟙_ _)).isStrictlyGE_iff (-b)).2
    intro j hj
    exact hz j ((P.isStrictlyLE_iff b).1 hb (-j) (by omega))
  · apply ((CochainComplex.moduleHomComplex P (𝟙_ _)).isStrictlyLE_iff (-a)).2
    intro j hj
    exact hz j ((P.isStrictlyGE_iff a).1 ha (-j) (by omega))

private theorem signed_dual_scalar {F G : Type u} [Field F] [Field G]
    (f : F →+* G) (P : CochainComplex (ModuleCat.{u} F) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (ht : ∀ i : ℤ, Module.Projective F (P.X i) ∧ Module.Finite F (P.X i)) :
    (∀ i : ℤ, Module.Finite F ((CochainComplex.moduleHomComplex P (𝟙_ _)).X i)) ∧
      Nonempty ((ihom ((DerivedCategory.fieldDerivedScalarExtension f).obj
          (DerivedCategory.Q.obj P))).obj (𝟙_ _) ≅
        (DerivedCategory.fieldDerivedScalarExtension f).obj (DerivedCategory.Q.obj
          (CochainComplex.moduleHomComplex P (𝟙_ _)))) := by
  obtain ⟨_, _, beta, _, _, _, _, _, _, hm, _⟩ :=
    CochainComplex.PerfectDualScalar.perfect_dual_scalar_calculus.{u}
  let f' : CommRingCat.of F ⟶ CommRingCat.of G := CommRingCat.ofHom f
  obtain ⟨hbeta, _, hdual, _⟩ := hm f' P a b ha hb ht
  let := hbeta
  let T : CochainComplex (ModuleCat.{u} F) ℤ ⥤
      CochainComplex (ModuleCat.{u} G) ℤ :=
    (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
  let := hb
  have hb' : (T.obj P).IsStrictlyLE b := by dsimp only [T]; infer_instance
  let e := (ModuleCat.extendScalars f).mapDerivedCategoryFactors.app P
  obtain ⟨ed⟩ := projective_model_dual (T.obj P) b hb' _ e
  refine ⟨fun i ↦ (hdual i).2, ⟨ed ≪≫ ?_⟩⟩
  exact DerivedCategory.Q.mapIso (asIso (beta f' P)).symm ≪≫
    ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app
      (CochainComplex.moduleHomComplex P (𝟙_ _))).symm

private theorem point_model {F : Type u} [Field F]
    (C : (DerivedCategory.pointFiniteDimensional F).FullSubcategory) :
    ∃ (P : CochainComplex (ModuleCat.{u} F) ℤ) (a b : ℤ),
      a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Projective F (P.X i) ∧ Module.Finite F (P.X i)) ∧
      Nonempty (C.obj ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨P, a, b, ha, hb, ht, e⟩ := pointFiniteDimensional_perfect C.property
  refine ⟨P, min a b, b, min_le_right _ _, ?_, hb, ht, e⟩
  apply (P.isStrictlyGE_iff _).2
  intro i hi
  exact (P.isStrictlyGE_iff a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))

private theorem qbar_family_bound (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (s : Finset (DerivedCategory.PointFdQbar l Ω)) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ B ∈ s,
      (∀ i : ℤ, FiniteDimensional Ω
        ((DerivedCategory.coefficientQbarCohomology l Ω i).obj B)) ∧
      ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.coefficientQbarCohomology l Ω i).obj B) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, le_rfl, by simp⟩
  | @insert B s hB ih =>
    obtain ⟨a, b, hab, hs⟩ := ih
    obtain ⟨t, ht⟩ := B.2.property.1
    obtain ⟨c, hc⟩ := t.bddBelow
    obtain ⟨d, hd⟩ := t.bddAbove
    refine ⟨min a c, max b d, (min_le_left _ _).trans (hab.trans (le_max_left _ _)), ?_⟩
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · refine ⟨fun i ↦ DerivedCategory.coefficientQbarCohomology_finite l Ω i A, ?_⟩
      intro i hi
      have hi' : i ∉ t := by
        intro hit
        have := hc hit
        have := hd hit
        rcases hi with hi | hi <;> omega
      dsimp only [DerivedCategory.coefficientQbarCohomology,
        DerivedCategory.PointFdQbarObjects, InducedCategory, Functor.copyObj_obj]
      exact (ModuleCat.extendScalars (R := A.1.val) (S := Ω) A.1.val.subtype).map_isZero (ht i hi')
    · refine ⟨(hs A hA).1, fun i hi ↦ (hs A hA).2 i ?_⟩
      rcases hi with hi | hi
      · exact Or.inl (lt_of_lt_of_le hi (min_le_left _ _))
      · exact Or.inr (lt_of_le_of_lt (le_max_left _ _) hi)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

attribute [local irreducible] integralImage integralOrdinarySections integralCompactSections
  rationalImage rationalOrdinarySections rationalCompactSections
  pointIntegralFibre pointRationalFibre sfIntegralCompactSupportValue
  sfRationalCompactSupportValue

private theorem rational_perfect_models
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (K_E : sfRationalConstructibleCategory l E X)
    (K_R : sfIntegralConstructibleCategory l E X)
    (_hrep : Nonempty ((sfRationalConstructibleLocalization l E X).obj K_R ≅ K_E)) :
    finiteTorConstructibleIntegral l E X K_R.obj ∧
    ∃ Pₛ Pₑ : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ,
      (∀ P ∈ ({Pₛ, Pₑ} : Set _),
        (∃ a b : ℤ, a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
        ∀ i : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
          Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i)) ∧
      Nonempty ((integralOrdinarySections D l hl E X K_R).obj ≅
        DerivedCategory.Q.{u + 1}.obj
          ((fieldCohomologyIntegralModelLift
            (Padic.coefficientExtensionIntegers l E)).obj Pₛ)) ∧
      Nonempty ((integralCompactSections D l hl E X c K_R).obj ≅
        DerivedCategory.Q.{u + 1}.obj
          ((fieldCohomologyIntegralModelLift
            (Padic.coefficientExtensionIntegers l E)).obj Pₑ)) ∧
      (∀ (P : CochainComplex (ModuleCat.{u}
          (Padic.coefficientExtensionIntegers l E)) ℤ)
          (C : DerivedCategory.{u} (ModuleCat.{u} E)),
        (P = Pₛ ∧ C = (rationalOrdinarySections D l hl E X K_E).obj) ∨
          (P = Pₑ ∧ C = (rationalCompactSections D l hl E X c K_E).obj) →
        Nonempty (C ≅ DerivedCategory.Q.{u}.obj
          (((ModuleCat.extendScalars.{u, u, u}
            (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapHomologicalComplex
              (.up ℤ)).obj P)) ∧
        Nonempty ((ihom C).obj (𝟙_ _) ≅ DerivedCategory.Q.{u}.obj
          (CochainComplex.moduleHomComplex
            (((ModuleCat.extendScalars.{u, u, u}
              (algebraMap (Padic.coefficientExtensionIntegers l E) E)).mapHomologicalComplex
                (.up ℤ)).obj P) (𝟙_ _)))) ∧
      ∀ C ∈ ({(rationalOrdinarySections D l hl E X K_E).obj,
          (rationalCompactSections D l hl E X c K_E).obj} : Set _),
        DerivedCategory.pointFiniteDimensional E C ∧
          DerivedCategory.pointFiniteDimensional E ((ihom C).obj (𝟙_ _)) := by
  classical
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    smoothQbarResidueInvertible D l hl X
  have hTor : finiteTorConstructibleIntegral l E X K_R.obj := by
    rw [← (integral_residue_tor D l hl E X).2]
    exact K_R.property
  obtain ⟨a, b, _, hlevels⟩ := hTor.2
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  obtain ⟨hs, he, _⟩ := integralSections_perfect_reduction D l hl E X
    c d hd K_R a b hlevels
  obtain ⟨Pₛ, hbs, hts, eis⟩ := DerivedCategory.small_perfect_coefficient_lift
    (Padic.coefficientExtensionIntegers l E)
    (integralOrdinarySections D l hl E X K_R).obj hs
  obtain ⟨Pₑ, hbe, hte, eie⟩ := DerivedCategory.small_perfect_coefficient_lift
    (Padic.coefficientExtensionIntegers l E)
    (integralCompactSections D l hl E X c K_R).obj he
  let T : CochainComplex (ModuleCat.{u}
      (Padic.coefficientExtensionIntegers l E)) ℤ ⥤
      CochainComplex (ModuleCat.{u} E) ℤ :=
    (ModuleCat.extendScalars.{u, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E)
    ).mapHomologicalComplex (.up ℤ)
  have erₛ : Nonempty ((rationalOrdinarySections D l hl E X K_E).obj ≅
      DerivedCategory.Q.obj (T.obj Pₛ)) :=
    (sections_rational_model_comparison D l hl E X c K_E K_R _hrep Pₛ).1 eis
  have erₑ : Nonempty ((rationalCompactSections D l hl E X c K_E).obj ≅
      DerivedCategory.Q.obj (T.obj Pₑ)) :=
    (sections_rational_model_comparison D l hl E X c K_E K_R _hrep Pₑ).2 eie
  have models (P : CochainComplex (ModuleCat.{u}
      (Padic.coefficientExtensionIntegers l E)) ℤ)
      (C : DerivedCategory.{u} (ModuleCat.{u} E))
      (hP : (P = Pₛ ∧ C = (rationalOrdinarySections D l hl E X K_E).obj) ∨
        (P = Pₑ ∧ C = (rationalCompactSections D l hl E X c K_E).obj)) :
      Nonempty (C ≅ DerivedCategory.Q.obj (T.obj P)) ∧
      Nonempty ((ihom C).obj (𝟙_ _) ≅ DerivedCategory.Q.obj
        (CochainComplex.moduleHomComplex (T.obj P) (𝟙_ _))) := by
    have hb : ∃ a b : ℤ, a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b := by
      rcases hP with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hbs
      · exact hbe
    have e : Nonempty (C ≅ DerivedCategory.Q.obj (T.obj P)) := by
      rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact erₛ
      · exact erₑ
    obtain ⟨_, b, _, _, hb⟩ := hb
    let := hb
    have : (T.obj P).IsStrictlyLE b := by
      dsimp only [T]
      infer_instance
    exact ⟨e, projective_model_dual (T.obj P) b this C e.some⟩
  refine ⟨hTor, Pₛ, Pₑ, ?_, eis, eie, models, ?_⟩
  · intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact ⟨hbs, hts⟩
    · exact ⟨hbe, hte⟩
  · intro C hC
    have hp : C.IsPerfect := by
      have data : ∃ P : CochainComplex (ModuleCat.{u}
          (Padic.coefficientExtensionIntegers l E)) ℤ,
          (∃ a b : ℤ, a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
          (∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i)) ∧
          Nonempty (C ≅ DerivedCategory.Q.obj (T.obj P)) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
        rcases hC with rfl | rfl
        · exact ⟨Pₛ, hbs, fun i ↦ (hts i).2, erₛ⟩
        · exact ⟨Pₑ, hbe, fun i ↦ (hte i).2, erₑ⟩
      obtain ⟨P, ⟨a, b, _, ha, hb⟩, ht, e⟩ := data
      let := ha
      let := hb
      refine ⟨T.obj P, a, b, ?_, ?_, ?_, e⟩
      · dsimp only [T]; infer_instance
      · dsimp only [T]; infer_instance
      · intro i
        have := ht i
        exact ⟨inferInstance, Module.Finite.base_change
          (Padic.coefficientExtensionIntegers l E) E (P.X i)⟩
    exact ⟨perfect_pointFiniteDimensional hp, perfect_pointFiniteDimensional hp.ihom_unit⟩

/-- Integral projective models, their rationalizations, and their signed dual models.
Source: blueprint thm-pod-point-perfectness.proof.md, Step 3
(blueprint: lem-sf-field-cohomology-perfect-descent).

Proof:
1. Raw rationalization has unchanged objects (def-weil-rationalization-karoubi).
   The residue Tor theorem (lem-coef-integral-residue-tor) places every integral
   representative in finiteTorConstructibleIntegral, uniformly over all reductions.
2. Finite type gives a finite dimension bound (lem-kun-dimension-finite-type), also
   for the empty scheme by choosing zero. Apply lem-sf-integral-sections-perfect-reduction
   and the bounded finite projective definition (def-pc-perfect-ring-complex) to both
   ordinary and compact sections. Finitely generated projectives admit small carriers;
   the displayed lift is the canonical coefficient/carrier transport.
3. The direct-image and compact-support rationalization conventions, followed by
   def-weil-finite-coefficient-point, identify the rational images with scalar extension
   of the integral images. The field is localization at the chosen uniformizer
   (lem-weil-l-adic-integers-localization-uniformizer). Exact scalar extension preserves
   the model quasi-isomorphisms (lem-pod-perfect-dual-scalar-calculus).
4. Apply lem-pod-projective-hom-evaluation-model to each bounded projective field model
   with target E[0]. Its Hom differential is d(f)=(-1)^(i+1) f d_P in degree i.
   This identifies the signed model with ordinary derived module Hom into E.
5. Kernels and quotients of finite-dimensional spaces are finite-dimensional.
   Bounded support of P and its reversed interval for the signed dual give bounded
   cohomology for all four rational point complexes. -/
theorem field_cohomology_perfect_descent_rational
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    (c : Compactification (X ↘ Spec (.of D.k)))
    (K_E : sfRationalConstructibleCategory l E.val X)
    (K_R : sfIntegralConstructibleCategory l E.val X)
    (_hrep : Nonempty ((sfRationalConstructibleLocalization l E.val X).obj K_R ≅ K_E)) :
    finiteTorConstructibleIntegral l E.val X K_R.obj ∧
    ∃ Pₛ Pₑ : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E.val)) ℤ,
      (∀ P ∈ ({Pₛ, Pₑ} : Set _),
        (∃ a b : ℤ, a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
        ∀ i : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E.val) (P.X i) ∧
          Module.Finite (Padic.coefficientExtensionIntegers l E.val) (P.X i)) ∧
      Nonempty ((integralOrdinarySections D l hl E.val X K_R).obj ≅
        DerivedCategory.Q.{u + 1}.obj
          ((fieldCohomologyIntegralModelLift
            (Padic.coefficientExtensionIntegers l E.val)).obj Pₛ)) ∧
      Nonempty ((integralCompactSections D l hl E.val X c K_R).obj ≅
        DerivedCategory.Q.{u + 1}.obj
          ((fieldCohomologyIntegralModelLift
            (Padic.coefficientExtensionIntegers l E.val)).obj Pₑ)) ∧
      (∀ (P : CochainComplex (ModuleCat.{u}
          (Padic.coefficientExtensionIntegers l E.val)) ℤ)
          (C : DerivedCategory.{u} (ModuleCat.{u} E.val)),
        (P = Pₛ ∧ C = (rationalOrdinarySections D l hl E.val X K_E).obj) ∨
          (P = Pₑ ∧ C = (rationalCompactSections D l hl E.val X c K_E).obj) →
        Nonempty (C ≅ DerivedCategory.Q.{u}.obj
          (((ModuleCat.extendScalars.{u, u, u}
            (algebraMap (Padic.coefficientExtensionIntegers l E.val) E.val)).mapHomologicalComplex
              (.up ℤ)).obj P)) ∧
        Nonempty ((ihom C).obj (𝟙_ _) ≅ DerivedCategory.Q.{u}.obj
          (CochainComplex.moduleHomComplex
            (((ModuleCat.extendScalars.{u, u, u}
              (algebraMap (Padic.coefficientExtensionIntegers l E.val) E.val)).mapHomologicalComplex
                (.up ℤ)).obj P) (𝟙_ _)))) ∧
      ∀ C ∈ ({(rationalOrdinarySections D l hl E.val X K_E).obj,
          (rationalCompactSections D l hl E.val X c K_E).obj} : Set _),
        DerivedCategory.pointFiniteDimensional E.val C ∧
          DerivedCategory.pointFiniteDimensional E.val ((ihom C).obj (𝟙_ _)) := by
  exact rational_perfect_models D l hl X E.val c K_E K_R _hrep

set_option maxHeartbeats 1600000 in
-- The four model witnesses and their stagewise comparisons require extra elaboration fuel.
/-- One finite coefficient stage represents both point complexes and their signed duals.
Source: blueprint thm-pod-point-perfectness.proof.md, Step 3
(blueprint: lem-sf-field-cohomology-perfect-descent).

Proof:
1. Every object of def-weil-algebraically-closed-coefficients is an actual finite-stage
   pair. Choose that stage F and its rational object K_F; no idempotent completion
   or Weil structure is involved.
2. The rational point fibres already belong to the finite-dimensional bounded
   point category. Transport them along the canonical Shrink algebra equivalence
   to F itself, and apply the proved field-perfectness criterion to obtain bounded
   finite-dimensional models Cₛ and Cₑ. The stagewise fibre object formula identifies
   their pairs with the ordinary and compact sections.
3. Form the signed moduleHomComplex into F[0] at F. Its degree i term is the dual
   of the degree -i term of the original complex, so it is finite-dimensional and
   supported on the reflected interval. The projective Hom evaluation model
   identifies its realization with the ordinary module derived dual.
4. Apply the beta isomorphism of lem-pod-perfect-dual-scalar-calculus and the exact
   scalar-extension comparison on complexes. They identify the signed dual after
   extension to Ω with the derived dual of the scalar-extended model. Transport
   this along the two point-category presentation isomorphisms.
5. By def-weil-coefficient-cohomology-modules their cohomology is scalar extension of
   finite-stage cohomology. A finite spanning set stays spanning after scalar extension;
   tensoring a zero space gives zero. Bounded supports of Cₛ and Cₑ and their reflected
   dual supports yield one finite interval for all four objects. -/
theorem field_cohomology_perfect_descent_qbar
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    ∃ (F : Padic.FiniteCoefficientFields l Ω)
      (K_F : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X F)
      (Cₛ Cₑ : CochainComplex (ModuleCat.{u} F.val) ℤ)
      (hₛ : DerivedCategory.pointFiniteDimensional F.val (DerivedCategory.Q.{u}.obj Cₛ))
      (hₑ : DerivedCategory.pointFiniteDimensional F.val (DerivedCategory.Q.{u}.obj Cₑ))
      (hₛd : DerivedCategory.pointFiniteDimensional F.val (DerivedCategory.Q.{u}.obj
        (CochainComplex.moduleHomComplex Cₛ (𝟙_ _))))
      (hₑd : DerivedCategory.pointFiniteDimensional F.val (DerivedCategory.Q.{u}.obj
        (CochainComplex.moduleHomComplex Cₑ (𝟙_ _)))),
      Nonempty (K ≅ ⟨F, K_F⟩) ∧
      (∀ C ∈ ({Cₛ, Cₑ, CochainComplex.moduleHomComplex Cₛ (𝟙_ _),
          CochainComplex.moduleHomComplex Cₑ (𝟙_ _)} : Set _),
        (∃ a b : ℤ, a ≤ b ∧ C.IsStrictlyGE a ∧ C.IsStrictlyLE b) ∧
          ∀ i : ℤ, FiniteDimensional F.val (C.X i)) ∧
      Nonempty ((DerivedCategory.fieldDerivedScalarExtension
          (Shrink.algEquiv (Padic l) F.val).toRingHom).obj
          (rationalOrdinarySections D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X K_F).obj ≅
        DerivedCategory.Q.{u}.obj Cₛ) ∧
      Nonempty ((DerivedCategory.fieldDerivedScalarExtension
          (Shrink.algEquiv (Padic l) F.val).toRingHom).obj
          (rationalCompactSections D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X c K_F).obj ≅
        DerivedCategory.Q.{u}.obj Cₑ) ∧
      Nonempty (qbarOrdinarySections D l hl X Ω K ≅
        (⟨F, ⟨DerivedCategory.Q.{u}.obj Cₛ, hₛ⟩⟩ : DerivedCategory.PointFdQbar l Ω)) ∧
      Nonempty (qbarCompactSections D l hl X Ω c K ≅
        (⟨F, ⟨DerivedCategory.Q.{u}.obj Cₑ, hₑ⟩⟩ : DerivedCategory.PointFdQbar l Ω)) ∧
      Nonempty ((ihom ((DerivedCategory.pointFdQbarRealization l Ω).obj
          (qbarOrdinarySections D l hl X Ω K))).obj (𝟙_ _) ≅
        (DerivedCategory.pointFdQbarRealization l Ω).obj
          ⟨F, ⟨DerivedCategory.Q.{u}.obj (CochainComplex.moduleHomComplex Cₛ (𝟙_ _)), hₛd⟩⟩) ∧
      Nonempty ((ihom ((DerivedCategory.pointFdQbarRealization l Ω).obj
          (qbarCompactSections D l hl X Ω c K))).obj (𝟙_ _) ≅
        (DerivedCategory.pointFdQbarRealization l Ω).obj
          ⟨F, ⟨DerivedCategory.Q.{u}.obj (CochainComplex.moduleHomComplex Cₑ (𝟙_ _)), hₑd⟩⟩) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ B ∈ ({(⟨F, ⟨DerivedCategory.Q.{u}.obj Cₛ, hₛ⟩⟩ : DerivedCategory.PointFdQbar l Ω),
            ⟨F, ⟨DerivedCategory.Q.{u}.obj Cₑ, hₑ⟩⟩,
            ⟨F, ⟨DerivedCategory.Q.{u}.obj (CochainComplex.moduleHomComplex Cₛ (𝟙_ _)), hₛd⟩⟩,
            ⟨F, ⟨DerivedCategory.Q.{u}.obj (CochainComplex.moduleHomComplex Cₑ (𝟙_ _)), hₑd⟩⟩} :
          Set (DerivedCategory.PointFdQbar l Ω)),
          (∀ i : ℤ, FiniteDimensional Ω
            ((DerivedCategory.coefficientQbarCohomology l Ω i).obj B)) ∧
          ∀ i : ℤ, i < a ∨ b < i →
            IsZero ((DerivedCategory.coefficientQbarCohomology l Ω i).obj B) := by
  classical
  let F := K.stage
  let Aₛ := (DerivedCategory.pointFdScalarExtension
    (Shrink.algEquiv (Padic l) F.val).toRingHom).obj
      (rationalOrdinarySections D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X K.obj)
  let Aₑ := (DerivedCategory.pointFdScalarExtension
    (Shrink.algEquiv (Padic l) F.val).toRingHom).obj
      (rationalCompactSections D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X c K.obj)
  obtain ⟨Pₛ, aₛ, bₛ, habₛ, haₛ, hbₛ, htₛ, ⟨eₛ⟩⟩ := point_model Aₛ
  obtain ⟨Pₑ, aₑ, bₑ, habₑ, haₑ, hbₑ, htₑ, ⟨eₑ⟩⟩ := point_model Aₑ
  let := haₛ
  let := hbₛ
  let := haₑ
  let := hbₑ
  have hpₛ : (DerivedCategory.Q.obj Pₛ).IsPerfect :=
    DerivedCategory.isPerfect_Q_obj Pₛ aₛ bₛ htₛ
  have hpₑ : (DerivedCategory.Q.obj Pₑ).IsPerfect :=
    DerivedCategory.isPerfect_Q_obj Pₑ aₑ bₑ htₑ
  have hₛ := perfect_pointFiniteDimensional hpₛ
  have hₑ := perfect_pointFiniteDimensional hpₑ
  obtain ⟨hdtₛ, ⟨eds⟩⟩ := signed_dual_scalar F.val.subtype Pₛ aₛ bₛ haₛ hbₛ htₛ
  obtain ⟨hdtₑ, ⟨ede⟩⟩ := signed_dual_scalar F.val.subtype Pₑ aₑ bₑ haₑ hbₑ htₑ
  obtain ⟨hdloₛ, hdhiₛ⟩ := signed_dual_bounds Pₛ aₛ bₛ haₛ hbₛ
  obtain ⟨hdloₑ, hdhiₑ⟩ := signed_dual_bounds Pₑ aₑ bₑ haₑ hbₑ
  let := hdloₛ
  let := hdhiₛ
  let := hdloₑ
  let := hdhiₑ
  have hₛd : DerivedCategory.pointFiniteDimensional F.val (DerivedCategory.Q.obj
      (CochainComplex.moduleHomComplex Pₛ (𝟙_ _))) :=
    perfect_pointFiniteDimensional
      (DerivedCategory.isPerfect_Q_obj _ (-bₛ) (-aₛ)
        (fun i ↦ ⟨inferInstance, hdtₛ i⟩))
  have hₑd : DerivedCategory.pointFiniteDimensional F.val (DerivedCategory.Q.obj
      (CochainComplex.moduleHomComplex Pₑ (𝟙_ _))) :=
    perfect_pointFiniteDimensional
      (DerivedCategory.isPerfect_Q_obj _ (-bₑ) (-aₑ)
        (fun i ↦ ⟨inferInstance, hdtₑ i⟩))
  let Bₛ : DerivedCategory.PointFdQbar l Ω := ⟨F, ⟨DerivedCategory.Q.obj Pₛ, hₛ⟩⟩
  let Bₑ : DerivedCategory.PointFdQbar l Ω := ⟨F, ⟨DerivedCategory.Q.obj Pₑ, hₑ⟩⟩
  let Bₛd : DerivedCategory.PointFdQbar l Ω :=
    ⟨F, ⟨DerivedCategory.Q.obj (CochainComplex.moduleHomComplex Pₛ (𝟙_ _)), hₛd⟩⟩
  let Bₑd : DerivedCategory.PointFdQbar l Ω :=
    ⟨F, ⟨DerivedCategory.Q.obj (CochainComplex.moduleHomComplex Pₑ (𝟙_ _)), hₑd⟩⟩
  have es₀ : qbarOrdinarySections D l hl X Ω K ≅
      (DerivedCategory.pointFdQbarStage l Ω F).obj Aₛ := by
    apply eqToIso
    change ((pointQbarFibre_existsUnique D l hl Ω).exists.choose).obj _ = _
    rw [(pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1]
    dsimp only [pointQbarFibreObj, qbarImage, pointStageFibre,
      DerivedCategory.pointFdQbarStage, Functor.comp_obj, Aₛ, F]
    unfold rationalOrdinarySections
    rfl
  have ee₀ : qbarCompactSections D l hl X Ω c K ≅
      (DerivedCategory.pointFdQbarStage l Ω F).obj Aₑ := by
    apply eqToIso
    change ((pointQbarFibre_existsUnique D l hl Ω).exists.choose).obj _ = _
    rw [(pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1]
    dsimp only [pointQbarFibreObj, sfQbarCompactSupportValue, pointStageFibre,
      DerivedCategory.pointFdQbarStage, Functor.comp_obj, Aₑ, F]
    unfold rationalCompactSections
    rfl
  let es : qbarOrdinarySections D l hl X Ω K ≅ Bₛ :=
    es₀ ≪≫ (DerivedCategory.pointFdQbarStage l Ω F).mapIso
      ((DerivedCategory.pointFiniteDimensional F.val).isoMk eₛ)
  let ee : qbarCompactSections D l hl X Ω c K ≅ Bₑ :=
    ee₀ ≪≫ (DerivedCategory.pointFdQbarStage l Ω F).mapIso
      ((DerivedCategory.pointFiniteDimensional F.val).isoMk eₑ)
  refine ⟨F, K.obj, Pₛ, Pₑ, hₛ, hₑ, hₛd, hₑd, ⟨Iso.refl K⟩, ?_,
    ⟨eₛ⟩, ⟨eₑ⟩, ⟨es⟩, ⟨ee⟩, ?_, ?_, ?_⟩
  · intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact ⟨⟨aₛ, bₛ, habₛ, haₛ, hbₛ⟩, fun i ↦ (htₛ i).2⟩
    · exact ⟨⟨aₑ, bₑ, habₑ, haₑ, hbₑ⟩, fun i ↦ (htₑ i).2⟩
    · exact ⟨⟨-bₛ, -aₛ, by omega, hdloₛ, hdhiₛ⟩, hdtₛ⟩
    · exact ⟨⟨-bₑ, -aₑ, by omega, hdloₑ, hdhiₑ⟩, hdtₑ⟩
  · let er := (DerivedCategory.pointFdQbarRealization l Ω).mapIso es
    exact ⟨(asIso ((MonoidalClosed.pre er.hom).app (𝟙_ _))).symm ≪≫ eds⟩
  · let er := (DerivedCategory.pointFdQbarRealization l Ω).mapIso ee
    exact ⟨(asIso ((MonoidalClosed.pre er.hom).app (𝟙_ _))).symm ≪≫ ede⟩
  · obtain ⟨a, b, hab, h⟩ := qbar_family_bound l Ω {Bₛ, Bₑ, Bₛd, Bₑd}
    refine ⟨a, b, hab, fun B hB ↦ h B ?_⟩
    change B ∈ ({Bₛ, Bₑ, Bₛd, Bₑd} : Set _) at hB
    simpa only [Finset.mem_insert, Finset.mem_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] using hB

end WeilConjectures
