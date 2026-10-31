/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.ScalarModelRoosZeroLiftCore
import all WeilConjectures.TraceFormula.ScalarModelRoosZeroLiftCore
import Mathlib.Algebra.Homology.Double

/-! # Strictification of a scalar Roos map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})

-- STATEMENT-DISPUTED: preserving the first coordinates forces their Roos boundary to be
-- zero, which is not a consequence of K-flatness or flat terms. A free two-term identity
-- disk maps to any degree of the Roos complex; an incompatible tuple in that degree
-- cannot be preserved by a zero-shift map. See the proved obstruction checks below
-- and report.md for the coefficient-system example.
/-- Every scalar Roos map admits a strict zero-shift representative with the same
unshifted quotient coordinates.

Source: Stacks 06YY and 0941; Bhatt--Scholze, Definition 3.4.10.
(blueprint: lem-trf-scalar-model-roos-zero-lift-strictification)

Proof in words: transpose the compatible quotient family of the map through the
constant-tower/limit adjunction.  The transpose has zero shifted coordinate, and
its projections are the original unshifted Roos coordinates.  The quotient
transition equations and the chain-map equation establish compatibility in every
cochain degree; the universal property of the mapping cocone then assembles the
strict representative. -/
theorem scalarModelRoosZeroLift_strictify
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor) :
    ∃ f₀ : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor,
      (∀ i : ℤ, f₀.f i ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).v
          i (i - 1) (by omega) = 0) ∧
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ),
        (f₀.f i ≫ (CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U =
        (f.f i ≫ (CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U) := by
  sorry

-- These proved checks isolate the obstruction without using the disputed theorem.
-- They follow the disputed theorem so that its auxiliary proof names stay unchanged.
private theorem cocone_zeroLift_iff
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {K T M : CochainComplex A ℤ} (δ : K ⟶ T)
    (f : M ⟶ CochainComplex.mappingCocone δ) :
    (∃ g : M ⟶ CochainComplex.mappingCocone δ,
      (∀ i : ℤ, g.f i ≫
        (CochainComplex.mappingCocone.snd δ).v i (i - 1) (by omega) = 0) ∧
      g ≫ CochainComplex.mappingCocone.fst δ =
        f ≫ CochainComplex.mappingCocone.fst δ) ↔
      f ≫ CochainComplex.mappingCocone.fst δ ≫ δ = 0 := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    rw [← Category.assoc, ← hgf, Category.assoc]
    exact ScalarRoosLiftProof.cocone_fst_zero δ g hg
  · intro hf
    refine ⟨CochainComplex.mappingCocone.lift δ
      (f ≫ CochainComplex.mappingCocone.fst δ) 0 ?_, ?_, ?_⟩
    · simp only [Category.assoc, hf, CochainComplex.HomComplex.δ_zero,
        CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]
    · intro i
      exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ i (i - 1) (by omega)
    · exact CochainComplex.mappingCocone.lift_fst _ _ _ _

private theorem cocone_disk_obstruction
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    [HasZeroObject A] {K T : CochainComplex A ℤ} (δ : K ⟶ T)
    (i : ℤ) (V : A) (a : V ⟶ (CochainComplex.mappingCocone δ).X i)
    (ha : a ≫ (CochainComplex.mappingCocone.fst δ).f i ≫ δ.f i ≠ 0) :
    ∃ f : HomologicalComplex.double (𝟙 V)
        (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) ⟶
          CochainComplex.mappingCocone δ,
      ¬ ∃ g : HomologicalComplex.double (𝟙 V)
          (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) ⟶
            CochainComplex.mappingCocone δ,
        (∀ q : ℤ, g.f q ≫
          (CochainComplex.mappingCocone.snd δ).v q (q - 1) (by omega) = 0) ∧
        g ≫ CochainComplex.mappingCocone.fst δ =
          f ≫ CochainComplex.mappingCocone.fst δ := by
  let h : (ComplexShape.up ℤ).Rel i (i + 1) := by simp
  let f := HomologicalComplex.mkHomFromDouble (f := 𝟙 V) h (by omega : i ≠ i + 1)
    a (a ≫ (CochainComplex.mappingCocone δ).d i (i + 1)) (by simp)
      (by intro k _; simp only [Category.assoc, HomologicalComplex.d_comp_d, comp_zero])
  refine ⟨f, ?_⟩
  rw [cocone_zeroLift_iff]
  intro hf
  have hi := congrArg (fun k ↦ k.f i) hf
  dsimp only [f] at hi
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    HomologicalComplex.mkHomFromDouble_f₀, Category.assoc] at hi
  apply ha
  exact (cancel_epi (HomologicalComplex.doubleXIso₀ (𝟙 V) h).hom).1
    (by simpa only [comp_zero] using hi)

private theorem roos_disk_counterexample
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i : ℤ) (V : A)
    (b : V ⟶ (C.obj (op 0)).X i) (hb : b ≠ 0) :
    ∃ f : HomologicalComplex.double (𝟙 V)
        (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) ⟶ integralOperationsRoos C,
      ¬ ∃ g : HomologicalComplex.double (𝟙 V)
          (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) ⟶ integralOperationsRoos C,
        (∀ q : ℤ, g.f q ≫
          (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v
            q (q - 1) (by omega) = 0) ∧
        g ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) =
          f ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) := by
  let K := fun n : ℕ ↦ C.obj (op n)
  have hp : Pi.ι K 0 ≫ scalarRoosBoundary C ≫ Pi.π K 0 = 𝟙 _ := by
    dsimp only [K]
    have hδ := (towerTransitionEndomorphism_eq_iff
      (integralOperationsTowerStep C) (scalarRoosBoundary C)).mp rfl 0
    rw [hδ]
    simp only [Preadditive.comp_sub, Pi.ι_π_eq_id,
      Pi.ι_π_of_ne_assoc (fun n : ℕ ↦ C.obj (op n))
        (by omega : (0 : ℕ) ≠ 0 + 1), zero_comp, sub_zero]
  let a := b ≫ (Pi.ι K 0).f i ≫
    (CochainComplex.mappingCocone.inl (scalarRoosBoundary C)).v i i (add_zero i)
  apply cocone_disk_obstruction (scalarRoosBoundary C) i V a
  intro hz
  apply hb
  have h := congrArg (fun z ↦ z ≫ (Pi.π K 0).f i) hz
  dsimp only [a] at h
  simp only [Category.assoc, CochainComplex.mappingCocone.inl_v_fst_f_assoc,
    zero_comp] at h
  have hpi := congrArg (fun z ↦ z.f i) hp
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hpi
  rw [hpi] at h
  exact (Category.comp_id b).symm.trans h

-- Exact criterion for the unchanged existential conclusion above.
private theorem scalarStrictification_iff
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor) :
    (∃ f₀ : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor,
      (∀ i : ℤ, f₀.f i ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).v
          i (i - 1) (by omega) = 0) ∧
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ),
        (f₀.f i ≫ (CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U =
        (f.f i ≫ (CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U)) ↔
      f ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor) ≫
        scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor = 0 := by
  constructor
  · rintro ⟨g, hg, hcoord⟩
    apply (cocone_zeroLift_iff _ f).mp
    refine ⟨g, hg, ?_⟩
    apply Pi.hom_ext
    intro n
    ext i : 1
    ext U x
    exact congrArg (fun k ↦ k x) (hcoord n i U)
  · intro hb
    obtain ⟨g, hg, hgf⟩ := (cocone_zeroLift_iff _ f).mpr hb
    refine ⟨g, hg, ?_⟩
    intro n i U
    exact congrArg (fun k ↦ ((k ≫ Pi.π (fun m : ℕ ↦
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex
        (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U) hgf

end WeilConjectures
