/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorBasic
import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorComparison
import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorModels
import WeilConjectures.CategoryTheory.SystemEvaluationKFlat

/-! # Compatible normalized quotient error triangles

Source: blueprint sk-lem-sp-tower proof, second paragraph
(blueprint: lem-sp-normalized-quotient-error-triangle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
namespace SheafOfModules.NormalizedQuotientError
variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

private def normalizationNatTrans (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}) {m n : ℕ} (h : m ≤ n) :
    derivedSystemEvaluation B n ⋙ systemDerivedTensor A B h ⟶
      derivedSystemEvaluation B m where
  app C := normalization A B C h
  naturality {C D} f := by
    exact (systemDerivedTensorAdj A B h).homEquiv_naturality_right_square
      ((derivedSystemEvaluation B n).map f)
      ((systemDerivedTransition B h).app D)
      ((systemDerivedTransition B h).app C)
      ((derivedSystemEvaluation B m).map f)
      ((systemDerivedTransition B h).naturality f)

private theorem normalization_isIso_of_iso (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    {C D : DerivedCategory (StrictRingSystem B)} (e : C ≅ D)
    {m n : ℕ} (h : m ≤ n) (hD : IsIso (normalization A B D h)) :
    IsIso (normalization A B C h) := by
  exact (NatTrans.isIso_app_iff_of_iso (normalizationNatTrans A B h) e).2 hD

private theorem shiftedTwistMap_quasiIso (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    {V W : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (f : V ⟶ W) (hf : QuasiIso f) :
    QuasiIso (shiftedTwistMap R t f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  have hfn := (HomologicalComplex.quasiIso_iff_evaluation f).1 hf n
  change QuasiIso ((shiftFunctor (CochainComplex (Modules R) ℤ) (1 : ℤ)).map
    ((((CategoryTheory.evaluation ℕᵒᵖ (Modules R)).obj n).mapHomologicalComplex (.up ℤ)).map f))
  have := hfn
  infer_instance

private theorem normalization_rep (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (P : CochainComplex (StrictRingSystem B) ℤ) {m n : ℕ} (h : m ≤ n) :
    (systemDerivedTensor A B h).map
        ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app P) ≫
      (A (B.map (homOfLE h).op)).model.ε.app (level B P n) ≫
      DerivedCategory.Q.map (ordinaryNormalization A B P h) =
    normalization A B (DerivedCategory.Q.obj P) h ≫
      (systemEvaluation B m).mapDerivedCategoryFactors.hom.app P := by
  let D := A (B.map (homOfLE h).op)
  let Rb := systemRestriction B h
  let en := (systemEvaluation B n).mapDerivedCategoryFactors.app P
  let em := (systemEvaluation B m).mapDerivedCategoryFactors.app P
  let er := Rb.mapDerivedCategoryFactors.app (level B P m)
  have ho : ((D.ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv _ _)
      (ordinaryNormalization A B P h) = transition B P h := by
    dsimp only [ordinaryNormalization, systemTensorAdj, systemTensor, D]
    rw [Equiv.apply_symm_apply]
    apply HomologicalComplex.hom_ext
    intro i
    exact Category.comp_id _
  have ht := D.transpose (level B P n) (level B P m) (ordinaryNormalization A B P h)
  rw [ho] at ht
  apply (D.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  erw [ht]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [normalization, systemDerivedTensorAdj, D]
  erw [Equiv.apply_symm_apply]
  change en.hom ≫ (DerivedCategory.Q.map (transition B P h) ≫ er.inv) =
    (systemDerivedTransition B h).app (DerivedCategory.Q.obj P) ≫
      Rb.mapDerivedCategory.map em.hom
  apply (cancel_mono er.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (systemDerivedTransition_rep B h P).symm

private theorem ordinaryNormalization_quasiIso (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (P : CochainComplex (StrictRingSystem B) ℤ) (hP : systemComponentwiseKFlat B P)
    {m n : ℕ} (h : m ≤ n)
    (hC : IsIso (normalization A B (DerivedCategory.Q.obj P) h)) :
    QuasiIso (ordinaryNormalization A B P h) := by
  let D := A (B.map (homOfLE h).op)
  have : IsIso (D.model.ε.app (level B P n)) := D.model.computes _ (hP n).1
  have htotal : IsIso ((systemDerivedTensor A B h).map
        ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app P) ≫
      D.model.ε.app (level B P n) ≫
      DerivedCategory.Q.map (ordinaryNormalization A B P h)) := by
    rw [normalization_rep A B P h]
    have := hC
    infer_instance
  have : IsIso (((systemDerivedTensor A B h).map
        ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app P) ≫
      D.model.ε.app (level B P n)) ≫
      DerivedCategory.Q.map (ordinaryNormalization A B P h)) := by
    simpa only [Category.assoc] using htotal
  have : IsIso (DerivedCategory.Q.map (ordinaryNormalization A B P h)) :=
    IsIso.of_isIso_comp_left
      ((systemDerivedTensor A B h).map
        ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app P) ≫
        D.model.ε.app (level B P n)) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 this

private theorem model_normalization_quasiIso (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (hP : systemComponentwiseKFlat B P)
    (C : DerivedCategory (StrictRingSystem B)) (e : DerivedCategory.Q.obj P ≅ C)
    (hC : ∀ m n (h : m ≤ n), IsIso (normalization A B C h))
    (m : ℕ) (M : QuotientModel R t B a A P m) : QuasiIso M.N := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  have hn : IsIso (normalization A B (DerivedCategory.Q.obj P)
      (Nat.le_add_right m n.unop)) :=
    normalization_isIso_of_iso A B e _ (hC _ _ _)
  have : QuasiIso (ordinaryNormalization A B P (Nat.le_add_right m n.unop)) :=
    ordinaryNormalization_quasiIso A B P hP _ hn
  change QuasiIso ((towerViewMap R M.N).app (op n.unop))
  rw [M.N_eq]
  infer_instance

private def assemble (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (P : CochainComplex (StrictRingSystem B) ℤ) (m : ℕ)
    (M : QuotientModel R t B a A P m) (E : ErrorComparisonMap R t B a A P m M)
    (hE : QuasiIso E.j) (hN : QuasiIso M.N) : ErrorTriangle R t B a A P m := by
  letI : QuasiIso M.N := hN
  letI : QuasiIso (shiftedTwistMap R t M.N) := shiftedTwistMap_quasiIso R t M.N hN
  letI : QuasiIso E.j := hE
  exact {
    V := M.V
    ν := M.ν
    μ := M.μ
    μ_unit := M.μ_unit
    augmentation := M.augmentation
    augmentation_inr := M.augmentation_inr
    augmentation_inl := M.augmentation_inl
    ε := M.ε
    ε_eq := M.ε_eq
    N := M.N
    N_eq := M.N_eq
    N_quasiIso := hN
    j := E.j
    j_quasiIso := hE
    j_generator := E.j_generator
    j_target := E.j_target
    errorIso := (asIso (DerivedCategory.Q.map (shiftedTwistMap R t M.N))).symm ≪≫
      asIso (DerivedCategory.Q.map E.j)
    errorIso_eq := by simp
    distinguished := DerivedCategory.mappingCocone_triangle_distinguished M.ε }

private theorem exists_of_models (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B) (A : SystemScalarAssignment (J := J))
    (C : DerivedCategory (StrictRingSystem B))
    (hC : ∀ m n (h : m ≤ n), IsIso (normalization A B C h)) (m : ℕ)
    (hM : ∀ P : CochainComplex (StrictRingSystem B) ℤ,
      Nonempty (QuotientModel R t B a A P m))
    (hE : ∀ P : CochainComplex (StrictRingSystem B) ℤ, systemComponentwiseKFlat B P →
      ∀ M : QuotientModel R t B a A P m,
        ∃ E : ErrorComparisonMap R t B a A P m M, QuasiIso E.j) :
    ∃ (P : CochainComplex (StrictRingSystem B) ℤ) (_e : DerivedCategory.Q.obj P ≅ C),
      systemComponentwiseKFlat B P ∧ Nonempty (ErrorTriangle R t B a A P m) := by
  classical
  obtain ⟨P, f, hP, hf⟩ := strictRingSystem_kFlatResolution B (DerivedCategory.Q.objPreimage C)
  have : QuasiIso f := hf
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso C
  obtain ⟨M⟩ := hM P
  obtain ⟨E, hE⟩ := hE P hP M
  exact ⟨P, e, hP, ⟨assemble R t B a A P m M E hE
    (model_normalization_quasiIso R t B a A P hP C e hC m M)⟩⟩


set_option maxHeartbeats 1600000 in
-- Comparing ordinary and derived transition adjuncts unfolds nested scalar functors.
set_option linter.unusedVariables false in
-- Keep the original existential witness name in the unchanged theorem statement.
/-- Compatible quotient error triangle for a normalized coefficient system.
Source: blueprint sk-lem-sp-tower proof, second paragraph
(blueprint: lem-sp-normalized-quotient-error-triangle).

Proof: choose a simultaneous flat-term K-flat representative by
lem-pur-system-evaluation-kflat and construct its ordinary quotient tensor model.
The normalized scalar adjunctions retain the original transition adjuncts. The
Koszul error-map construction gives j with its prescribed component formulas;
the principal-regular quotient calculation and K-flat tensoring make it a
quasi-isomorphism. Naturality of the derived transition adjuncts transports the
normalization hypothesis from C to Q(P). Compatibility of ordinary and derived
adjunctions identifies the image of ordinaryNormalization with that actual
normalization, up to the canonical evaluation and K-flat computation isomorphisms.
Thus ordinaryNormalization is a quasi-isomorphism. Exact scalar restriction and
levelwise detection make the whole-system N a quasi-isomorphism. Shifting and
scalar-twisting retain this property. Invert Q(shiftedTwistMap N) and compose with
Q(j) to obtain errorIso and its required equality. Finally the actual mapping
cocone triangle is distinguished under the derived localization functor. -/
theorem exists_errorTriangle (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : Mono ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (a : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    (q : ∀ n : ℕ, B.obj (op n) ≅ principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : ∀ n : ℕ, a.app (op n) ≫ (q n).hom =
      principalPowerRingProjection R (ringSection R t) (n + 1))
    (A : SystemScalarAssignment (J := J))
    (C : DerivedCategory (StrictRingSystem B))
    (hC : ∀ (m n : ℕ) (h : m ≤ n), IsIso (normalization A B C h))
    (m : ℕ) :
    ∃ (P : CochainComplex (StrictRingSystem B) ℤ) (e : DerivedCategory.Q.obj P ≅ C),
      systemComponentwiseKFlat B P ∧ Nonempty (ErrorTriangle R t B a A P m) := by
  apply exists_of_models R t B a A C hC m
  · exact fun P ↦ exists_quotientModel R t B a q hq A P m
  · intro P hP M
    obtain ⟨E⟩ := exists_errorComparisonMap R t B a q hq A P m M
    exact ⟨E, errorComparisonMap_quasiIso R t ht B a q hq A P hP m M E⟩

end SheafOfModules.NormalizedQuotientError
