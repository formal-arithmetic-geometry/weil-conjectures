/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The categorical trace of a chain endomorphism is the supertrace

Let `C` be a braided monoidal preadditive category and `K` a bounded cochain complex in `C`
whose terms have right duals, so that `K` is paired with its termwise dual `K^∨`
(`CochainComplex.exactPairingRightDual`). For the Koszul braiding of cochain complexes, the
categorical trace of a chain endomorphism `v : K ⟶ K` is, in degree `0`, the supertrace
`∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)` (`CochainComplex.trace_f_zero`): on the summand `Kᵖ ⊗ (K^∨)⁻ᵖ` the
Koszul sign of the braiding is `(-1)^(p · (-p)) = (-1)ᵖ`.

The supertrace only depends on the homotopy class of `v`
(`Homotopy.sum_negOnePow_smul_eq`): this holds for any family of additive cyclic functions
on the endomorphisms of the terms, for instance the categorical traces of `C`
(`Homotopy.sum_negOnePow_smul_trace_eq`) or the traces of linear maps of finite free modules
(`Homotopy.sum_negOnePow_smul_linearMapTrace_eq`). In particular the categorical trace of a
chain endomorphism of a bounded complex only depends on its homotopy class
(`Homotopy.trace_eq`).

This is blueprint `lem-trf-chain-supertrace`; the fact that the evaluation and coevaluation are
maps of complexes satisfying the triangle identities is `CochainComplex.exactPairingRightDual`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CategoryTheory.MonoidalCategory

section

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]

/-- The categorical trace is additive (used for blueprint `lem-trf-chain-supertrace`). -/
lemma trace_add {X : C} [HasRightDual X] (f g : X ⟶ X) : trace (f + g) = trace f + trace g := by
  simp [trace]

/-- The categorical trace as an additive map (used for blueprint `lem-trf-chain-supertrace`). -/
noncomputable def traceAddMonoidHom (X : C) [HasRightDual X] : (X ⟶ X) →+ (𝟙_ C ⟶ 𝟙_ C) where
  toFun := trace
  map_zero' := by simp [trace]
  map_add' := trace_add

/-- The additive categorical trace is the trace (blueprint `lem-trf-chain-supertrace`). -/
@[simp]
lemma traceAddMonoidHom_apply {X : C} [HasRightDual X] (f : X ⟶ X) :
    traceAddMonoidHom X f = trace f := rfl

end

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- The trace of `f : Y ⟶ Y` may be computed with the dual of an object `X ≅ Y`
(used for blueprint `lem-trf-chain-supertrace`). -/
lemma trace_eq_of_iso_rightDual {X Y : C} [HasRightDual X] [HasRightDual Y] (e : X ≅ Y)
    (f : Y ⟶ Y) (g : Y ⟶ X) (hg : g = e.inv) :
    η_ X Xᘁ ≫ e.hom ▷ Xᘁ ≫ f ▷ Xᘁ ≫ (β_ Y Xᘁ).hom ≫ Xᘁ ◁ g ≫ ε_ X Xᘁ = trace f := by
  subst hg
  rw [← BraidedCategory.braiding_naturality_left_assoc, ← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, assoc]
  rw [← trace, trace_comp_comm, assoc, Iso.inv_hom_id, comp_id]

end CategoryTheory.MonoidalCategory

namespace Homotopy

variable {C : Type*} [Category* C] [Preadditive C] {K : CochainComplex C ℤ} {v v' : K ⟶ K}

end Homotopy

namespace CochainComplex

section

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] (K : CochainComplex C ℤ) [∀ n, HasRightDual (K.X n)]

/-- Blueprint `lem-trf-chain-supertrace`: the contribution of the summand `Kᵖ ⊗ (K^∨)⁻ᵖ` to the
trace of `v : K ⟶ K` is the trace of `vᵖ`. -/
lemma rightDual.coevPQ_comp_evalPQ (v : K ⟶ K) (p : ℤ) :
    coevPQ K p (-p) (add_neg_cancel p) ≫ v.f p ▷ K.rightDual.X (-p) ≫
      (β_ (K.X p) (K.rightDual.X (-p))).hom ≫ evalPQ K (-p) p (neg_add_cancel p) =
        trace (v.f p) := by
  simp only [coevPQ, evalPQ, assoc]
  exact trace_eq_of_iso_rightDual (K.XIsoOfEq (neg_neg p)) _ _
    (by simp [HomologicalComplex.XIsoOfEq])

end

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  (K : CochainComplex C ℤ) [∀ n, HasRightDual (K.X n)] (a b : ℤ) [K.IsStrictlyGE a]
  [K.IsStrictlyLE b]

/-- The right dual `K^∨` of a bounded complex `K` whose terms have right duals, for the exact
pairing `CochainComplex.exactPairingRightDual` (blueprint `lem-trf-chain-supertrace`). -/
@[instance_reducible]
noncomputable def hasRightDual : HasRightDual K :=
  letI := exactPairingRightDual K a b
  ⟨K.rightDual⟩

/-- The categorical trace of a chain endomorphism of a bounded complex `K`, for the right dual
`CochainComplex.hasRightDual` (blueprint `lem-trf-chain-supertrace`). -/
lemma trace_eq (v : K ⟶ K) :
    letI := hasRightDual K a b
    trace v = rightDual.coev K a b ≫ v ▷ K.rightDual ≫ (β_ K K.rightDual).hom ≫
      rightDual.eval K := rfl

/-- Blueprint `lem-trf-chain-supertrace` (c): the categorical trace of a chain endomorphism `v`
of a bounded complex `K`, with respect to the Koszul braiding and the termwise dual `K^∨`, is the
supertrace `∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)`, as an endomorphism of `(𝟙_).X 0 ≅ 𝟙_ C`. -/
theorem trace_f_zero (v : K ⟶ K) :
    letI := hasRightDual K a b
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫ (trace v).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom =
      ∑ p ∈ Finset.Icc a b, (p.negOnePow : ℤ) • trace (v.f p) := by
  let := hasRightDual K a b
  simp only [trace_eq, HomologicalComplex.comp_f, assoc]
  rw [reassoc_of% rightDual.singleObjXSelf_inv_coev_f, rightDual.coevZero, Preadditive.sum_comp]
  refine Finset.sum_congr rfl (fun p _ ↦ ?_)
  rw [assoc, Monoidal.ι_whiskerRight_assoc]
  erw [Monoidal.ι_braiding_hom_assoc]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  simp only [assoc]
  rw [reassoc_of% rightDual.ι_eval_f, Iso.inv_hom_id, comp_id, mul_neg, Int.negOnePow_neg,
    Int.negOnePow_mul_self, ← rightDual.coevPQ_comp_evalPQ K v p]

/-- Blueprint `lem-trf-chain-supertrace` (c): the categorical trace of a chain endomorphism `v`
of a bounded complex `K` is the supertrace `∑ₚ (-1)ᵖ tr(vᵖ | Kᵖ)`, placed in degree `0` of the
unit complex. -/
theorem trace_f_zero_eq (v : K ⟶ K) :
    letI := hasRightDual K a b
    (trace v).f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫
      (∑ p ∈ Finset.Icc a b, (p.negOnePow : ℤ) • trace (v.f p)) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv := by
  rw [← trace_f_zero]
  simp

end CochainComplex

namespace Homotopy

open CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  {K : CochainComplex C ℤ} [∀ n, HasRightDual (K.X n)]

end Homotopy
