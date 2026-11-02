/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.OrdinaryScalarTowerProof
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryAssociationChain
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction

/-! # Degreewise strict association data

This is the finite balanced-tensor and transition part of the strict quotient
association.  The complex assembly is proved by the parent module.
(blueprint: stage3-pur-scalar-quotient-association-degree-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
attribute [local irreducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.integralScalarReduction WeilConjectures.scalarReductionExtension
  WeilConjectures.coefficientSequenceRestriction
  WeilConjectures.completedIntegralCommRingProjectionUnrestricted CategoryTheory.constantSheaf
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The glued ordinary association chain sends scalar multiples of quotient units to the
specified direct-model sections.

Source: Stacks Tags 03D7 and 03EK; the finite balanced association
(blueprint: stage3-pur-scalar-quotient-association-degree-data).

Proof: evaluate the chain isomorphism at level n. Its defining equation identifies
it with the finite balanced comparison followed by the inverse direct evaluation,
and the finite comparison sends c times the evaluated quotient unit of x to the
tensor c ⊗ x. -/
private theorem chainSection (W : Scheme.{u})
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (htransition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation) :
    letI := coefficientScalarModelZero A.scalar
    ∃ β : (integralOperationsGoodComplex l E W).ι ⋙ M.quotient l E W ⋙
        A.scalar.model.E.mapHomologicalComplex (.up ℤ) ≅ direct,
      ∀ (K : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : W.ProEtᵒᵖ)
        (c : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
        (x : (K.obj.X i).val.obj U),
        ((β.hom.app K).f i).val.app (op (n, U.unop))
          (c • (show (A.scalar.model.E.obj (M.tensor.obj (K.obj.X i))).val.obj
              (op (n, U.unop)) from
            (A.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (K.obj.X i))).val.app
              (op (n, U.unop))
              (CoefficientExtensionAssociation.quotientUnitSection l E W M
                (K.obj.X i) n U x))) =
        integralComparisonSequenceSection l L W ((direct.obj K).X i) n U
          ((((directEvaluation n).inv.app K).f i).val.app U
            (integralScalarTensorSection l E L ι W n (K.obj.X i) U c x)) := by
  classical
  obtain ⟨β, hβ⟩ := coefficientExtensionOrdinaryAssociationChain l E L ι W A M ρ hρ
    association hassociation direct directEvaluation htransition
  refine ⟨β, ?_⟩
  intro K n i U c x
  let X := K.obj.X i
  let q := CoefficientExtensionAssociation.quotientUnitSection l E W M X n U x
  have hu := OrdinaryScalarTowerProof.evaluatedUnit_smul_raw l E L ι W A ρ hρ
    (M.tensor.obj X) n U c q
  have hf := OrdinaryScalarTowerProof.finiteComparison_unit l E L ι W A M ρ association
    hassociation X n U c x
  have hi := congrArg (fun g ↦ g.f i) (hβ K n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hi
  have hm : (coefficientSequenceEvaluation l L W n).map ((β.hom.app K).f i) =
      (OrdinaryScalarTowerProof.finiteComparison l E L ι W A M ρ association n).hom.app X ≫
        ((directEvaluation n).inv.app K).f i := by
    have h1 : (coefficientSequenceEvaluation l L W n).map ((β.hom.app K).f i) =
        ((coefficientSequenceEvaluation l L W n).map ((β.hom.app K).f i) ≫
          ((directEvaluation n).hom.app K).f i) ≫ ((directEvaluation n).inv.app K).f i := by
      rw [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id_app,
        HomologicalComplex.id_f]
      exact (Category.comp_id _).symm
    rw [h1, hi]
    unfold coefficientExtensionAssociationChain
    rfl
  let y : (A.scalar.model.E.obj (M.tensor.obj X)).val.obj (op (n, U.unop)) :=
    c • (show (A.scalar.model.E.obj (M.tensor.obj X)).val.obj (op (n, U.unop)) from
      (A.scalar.ordinaryAdjunction.unit.app (M.tensor.obj X)).val.app (op (n, U.unop)) q)
  have hy : coefficientEvaluationSection l L W (A.scalar.model.E.obj (M.tensor.obj X)) n U y =
      c • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ
        (M.tensor.obj X) n U q :=
    eq_of_heq ((OrdinaryScalarTowerProof.evaluation_section_heq l L _ n U y).trans hu)
  have hmap : ((coefficientSequenceEvaluation l L W n).map ((β.hom.app K).f i)).val.app U
        (coefficientEvaluationSection l L W (A.scalar.model.E.obj (M.tensor.obj X)) n U y) =
      coefficientEvaluationSection l L W ((direct.obj K).X i) n U
        (((β.hom.app K).f i).val.app (op (n, U.unop)) y) :=
    OrdinaryScalarTowerProof.evaluation_map_section l L ((β.hom.app K).f i) n U y
  rw [hy, hm] at hmap
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hmap
  have hmap2 := hmap.symm.trans
    (congrArg (fun z ↦ ((((directEvaluation n).inv.app K).f i).val.app U) z) hf)
  exact eq_of_heq ((OrdinaryScalarTowerProof.evaluation_section_heq l L _ n U _).symm.trans
    ((heq_of_eq hmap2).trans
      (OrdinaryScalarTowerProof.sequenceSection_heq l L W _ n U _).symm))

/-- Equal zero-preserving functors give equal termwise images of a cochain complex.
Source: functoriality of termwise application (blueprint:
stage3-pur-scalar-quotient-association-degree-data). -/
private theorem mapHomologicalComplex_obj_eq {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (h : F = G)
    (X : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj X = (G.mapHomologicalComplex (.up ℤ)).obj X := by
  subst h
  rfl

/-- Balancing in the sequence-site scalar extension: `b ⊗ (a • y) = (ι(a) * b) ⊗ y`.
Source: Stacks 03EK, the balanced tensor product
(blueprint: stage3-pur-scalar-quotient-association-degree-data). -/
private theorem tensorSection_smul (W : Scheme.{u})
    (N : coefficientSequenceModules.{u, u} l E W) (V : (ℕ × W.ProEt)ᵒᵖ)
    (b : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj V)
    (a : (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj V) (y : N.val.obj V) :
    integralComparisonSequenceTensorSection l E L ι W N V b (a • y) =
      integralComparisonSequenceTensorSection l E L ι W N V
        ((integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom.app V a * b) y := by
  unfold integralComparisonSequenceTensorSection
  rw [← TensorProduct.smul_tmul]
  rfl

set_option maxHeartbeats 1600000 in
-- Instantiating the glued chain at the identity coefficient field elaborates large types.
/-- Degreewise normalized association datum for fixed strict quotient representatives.

Source: Stacks Tags 03EL and 07A4; the finite balanced tensor association and its
successor compatibility.  The finite association is evaluated through the two
`directEvaluation` isomorphisms, and the resulting maps are compatible with the
cochain differentials.  The proof is the generator calculation: the map sends
`b ⊗ (a ⊗ x)` to `(ι(a) * b) ⊗ x`; balancing, unit identities, and the fact that
coefficient reduction is a ring map prove the inverse, differential, and transition
identities.  This statement is strictly degreewise; the parent theorem performs
the whole-complex assembly.
(blueprint: stage3-pur-scalar-quotient-association-degree-data). -/
theorem quotientAssociation_degreeData_exists
    (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (d0 : CoefficientExtensionReductionData.{u, u} l E E (AlgHom.id ℚ_[l] E) W SE SE A0)
    (K : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory) :
    ∃ (δ : ∀ i : ℤ, ((scalar l E L ι W).obj (d0.direct.obj K)).X i ≅
        (d.direct.obj K).X i),
      (∀ (i j : ℤ),
        (δ i).hom ≫ (d.direct.obj K).d i j =
          ((scalar l E L ι W).obj (d0.direct.obj K)).d i j ≫ (δ j).hom) ∧
      ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
        (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
        (a : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, U.unop)))
        (x : (K.obj.X i).val.obj U),
        (δ i).hom.val.app (op (n, U.unop))
          (integralComparisonSequenceTensorSection l E L ι W ((d0.direct.obj K).X i)
            (op (n, U.unop)) b
            (integralComparisonSequenceSection.{u, u} l E W ((d0.direct.obj K).X i) n U
              ((((d0.directEvaluation n).inv.app K).f i).val.app U
                (integralScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W n
                  (K.obj.X i) U a x)))) =
        integralComparisonSequenceSection.{u, u} l L W ((d.direct.obj K).X i) n U
          ((((d.directEvaluation n).inv.app K).f i).val.app U
            (integralScalarTensorSection.{u, u} l E L ι W n (K.obj.X i) U
              (((integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom.app
                (op (n, U.unop))) a * b) x)) := by
  classical
  obtain ⟨M⟩ := CompletionUnit.ordinaryModel_exists l E W
  obtain ⟨A₁, hA₁, hT₁⟩ := OrdinaryScalarTowerProof.fixedSystems_exists l E L ι W
  obtain ⟨ρ₁, hρ₁, -⟩ := coefficientScalarCochainEvaluation l E L ι W A₁
  obtain ⟨f₁⟩ := coefficientExtensionFiniteAssociation_exists l E L ι W A₁
  obtain ⟨β₁, hβ₁⟩ := chainSection l E L ι W A₁ M ρ₁ hρ₁ f₁.association
    f₁.association_section d.direct d.directEvaluation d.direct_transition
  obtain ⟨A₀, hA₀, hT₀⟩ :=
    OrdinaryScalarTowerProof.fixedSystems_exists l E E (AlgHom.id ℚ_[l] E) W
  obtain ⟨ρ₀, hρ₀, -⟩ := coefficientScalarCochainEvaluation l E E (AlgHom.id ℚ_[l] E) W A₀
  obtain ⟨f₀⟩ := coefficientExtensionFiniteAssociation_exists l E E (AlgHom.id ℚ_[l] E) W A₀
  obtain ⟨β₀, hβ₀⟩ := chainSection l E E (AlgHom.id ℚ_[l] E) W A₀ M ρ₀ hρ₀ f₀.association
    f₀.association_section d0.direct d0.directEvaluation d0.direct_transition
  let _ := coefficientScalarModelZero A₁.scalar
  let _ := coefficientScalarModelZero A₀.scalar
  let Q := (M.quotient l E W).obj K.obj
  have hQ₀ := mapHomologicalComplex_obj_eq hA₀ Q
  have hQ₁ := (mapHomologicalComplex_obj_eq hA₁ Q).symm
  let γ : d0.direct.obj K ≅ Q :=
    (β₀.app K).symm ≪≫ eqToIso hQ₀ ≪≫ (scalarUnit l E W).app Q
  let Δ : (scalar l E L ι W).obj (d0.direct.obj K) ≅ d.direct.obj K :=
    (scalar l E L ι W).mapIso γ ≪≫ eqToIso hQ₁ ≪≫ β₁.app K
  refine ⟨fun i ↦ HomologicalComplex.Hom.isoApp Δ i, fun i j ↦ Δ.hom.comm i j, ?_⟩
  intro n i U b a x
  let V : (ℕ × W.ProEt)ᵒᵖ := op (n, U.unop)
  let q : (Q.X i).val.obj V :=
    CoefficientExtensionAssociation.quotientUnitSection l E W M (K.obj.X i) n U x
  let s₀ := integralComparisonSequenceSection.{u, u} l E W ((d0.direct.obj K).X i) n U
    ((((d0.directEvaluation n).inv.app K).f i).val.app U
      (integralScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W n
        (K.obj.X i) U a x))
  -- the identity-coefficient side
  have h₀ := hβ₀ K n i U a x
  have hinv : ((β₀.inv.app K).f i).val.app V s₀ =
      a • (show (A₀.scalar.model.E.obj (M.tensor.obj (K.obj.X i))).val.obj V from
        (A₀.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (K.obj.X i))).val.app V q) := by
    have hc : (β₀.hom.app K).f i ≫ (β₀.inv.app K).f i = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id_app, HomologicalComplex.id_f]
    refine (congrArg (fun y ↦ ((β₀.inv.app K).f i).val.app V y) h₀.symm).trans ?_
    exact congrArg (fun g ↦ g.val.app V (a • (show (A₀.scalar.model.E.obj
      (M.tensor.obj (K.obj.X i))).val.obj V from
        (A₀.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (K.obj.X i))).val.app V q))) hc
  have he₀ : ((eqToHom hQ₀).f i).val.app V
      (a • (show (A₀.scalar.model.E.obj (M.tensor.obj (K.obj.X i))).val.obj V from
        (A₀.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (K.obj.X i))).val.app V q)) =
      integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E) W (Q.X i) V a q := by
    rw [HomologicalComplex.eqToHom_f]
    exact eq_of_heq ((OrdinaryScalarTowerProof.eqToHom_section _ V _).trans
      (hT₀ (Q.X i) V a q).symm)
  have hγ : ((γ.hom).f i).val.app V s₀ = a • q :=
    (congrArg (fun z ↦ ((((scalarUnit l E W).hom.app Q).f i).val.app V z))
      ((congrArg (fun z ↦ ((eqToHom hQ₀).f i).val.app V z) hinv).trans he₀)).trans
      (scalar_unit_section l E W (Q.X i) V a q)
  -- the scalar side
  have he₁ : ((eqToHom hQ₁).f i).val.app V
      (integralComparisonSequenceTensorSection l E L ι W (Q.X i) V
        ((integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom.app V a * b) q) =
      ((integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom.app V a * b) •
        (show (A₁.scalar.model.E.obj (M.tensor.obj (K.obj.X i))).val.obj V from
          (A₁.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (K.obj.X i))).val.app V q) := by
    rw [HomologicalComplex.eqToHom_f]
    exact eq_of_heq ((OrdinaryScalarTowerProof.eqToHom_section _ V _).trans
      (hT₁ (Q.X i) V _ q))
  change ((Δ.hom).f i).val.app V
      (integralComparisonSequenceTensorSection l E L ι W ((d0.direct.obj K).X i) V b s₀) = _
  simp only [Δ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [scalar_section_naturality l E L ι W, hγ, tensorSection_smul l E L ι W, he₁]
  exact hβ₁ K n i U _ x

end WeilConjectures.ScalarExtensionTower
