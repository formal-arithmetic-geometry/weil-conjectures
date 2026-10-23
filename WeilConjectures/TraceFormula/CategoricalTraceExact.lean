/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Trace.LongExact
public import WeilConjectures.TraceFormula.CategoricalTrace
public import WeilConjectures.TraceFormula.UnitBasis

/-!

# Additivity of categorical traces along long exact sequences

Let `C` be an abelian braided monoidal category whose tensor product is additive, and such that
`K = End (𝟙_ C)` is a field: every nonzero endomorphism of the unit is invertible. An object is
*finite free* (`CategoryTheory.MonoidalCategory.IsFiniteFree`) if it is a finite biproduct of
copies of the unit `𝟙_ C`. Finite free objects are dualizable, morphisms between them are matrices
over `K`, and the categorical trace of an endomorphism is the trace of its matrix.

For a bounded long exact sequence
`⋯ ⟶ Aʲ ⟶ Bʲ ⟶ Dʲ ⟶ Aʲ⁺¹ ⟶ ⋯` of finite free objects with endomorphisms commuting with all
the maps, the alternating sums of the traces satisfy `STr(B) = STr(A) + STr(D)`
(`CategoryTheory.superTrace_eq_add_of_exact`).

## Main definitions

- `CategoryTheory.MonoidalCategory.IsFiniteFree`: finite biproducts of copies of the unit.

## Main results

- `CategoryTheory.superTrace_eq_add_of_exact`: additivity of supertraces along bounded long
  exact sequences of finite free objects.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- An object is *finite free* if it is isomorphic to a finite biproduct of copies of the
monoidal unit. -/
def MonoidalCategory.IsFiniteFree (X : C) : Prop :=
  ∃ n : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C)

omit [BraidedCategory C] [MonoidalPreadditive C] in
/-- A finite free object has a unit basis. -/
lemma MonoidalCategory.IsFiniteFree.exists_unitBasis {X : C} (hX : IsFiniteFree X) :
    ∃ n : ℕ, Nonempty (UnitBasis X (Fin n)) :=
  have ⟨n, ⟨e⟩⟩ := hX
  ⟨n, ⟨UnitBasis.ofIso e⟩⟩

/-- **Additivity of supertraces along long exact sequences.** Let `End (𝟙_ C)` be a field, and
let `⋯ ⟶ Aʲ ⟶ Bʲ ⟶ Dʲ ⟶ Aʲ⁺¹ ⟶ ⋯` be a long exact sequence of finite free objects, zero outside a
finite range of degrees, with endomorphisms `φ_A`, `φ_B`, `φ_D` commuting with all the maps.
Then `∑ⱼ (-1)ʲ Tr(φ_Bʲ) = ∑ⱼ (-1)ʲ Tr(φ_Aʲ) + ∑ⱼ (-1)ʲ Tr(φ_Dʲ)`. -/
theorem superTrace_eq_add_of_exact (hK : ∀ t : End (𝟙_ C), t ≠ 0 → IsIso t)
    (h₁ : (1 : End (𝟙_ C)) ≠ 0) {A B D : ℤ → C} (φA : ∀ j, A j ⟶ A j) (φB : ∀ j, B j ⟶ B j)
    (φD : ∀ j, D j ⟶ D j) (u : ∀ j, A j ⟶ B j) (v : ∀ j, B j ⟶ D j) (w : ∀ j, D j ⟶ A (j + 1))
    (hu : ∀ j, φA j ≫ u j = u j ≫ φB j) (hv : ∀ j, φB j ≫ v j = v j ≫ φD j)
    (hw : ∀ j, φD j ≫ w j = w j ≫ φA (j + 1))
    (huv : ∀ j, u j ≫ v j = 0) (hvw : ∀ j, v j ≫ w j = 0) (hwu : ∀ j, w j ≫ u (j + 1) = 0)
    (ex₁ : ∀ j, (ShortComplex.mk _ _ (huv j)).Exact)
    (ex₂ : ∀ j, (ShortComplex.mk _ _ (hvw j)).Exact)
    (ex₃ : ∀ j, (ShortComplex.mk _ _ (hwu j)).Exact)
    (hA : ∀ j, IsFiniteFree (A j)) (hB : ∀ j, IsFiniteFree (B j)) (hD : ∀ j, IsFiniteFree (D j))
    (hbdd : ∃ a b : ℤ, ∀ j, (j < a ∨ b < j) → IsZero (A j) ∧ IsZero (B j) ∧ IsZero (D j)) :
    superTrace B φB = superTrace A φA + superTrace D φD := by
  have hKf := isField_end_tensorUnit hK h₁
  let := hKf.toField
  have hfin {X : C} (hX : IsFiniteFree X) :
      FiniteDimensional (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) := by
    obtain ⟨n, ⟨b⟩⟩ := hX.exists_unitBasis
    exact b.moduleFinite
  have htr {X : C} (hX : IsFiniteFree X) (φ : X ⟶ X) :
      LinearMap.trace (End (𝟙_ C))ᵐᵒᵖ (𝟙_ C ⟶ X) (Preadditive.rightCompEndOp _ φ) =
        .op (categoricalTrace φ) := by
    obtain ⟨n, ⟨b⟩⟩ := hX.exists_unitBasis
    exact b.trace_rightCompEndOp φ
  have hex {X Y Z : C} (hX : IsFiniteFree X) (hY : IsFiniteFree Y) {f : X ⟶ Y} {g : Y ⟶ Z}
      {hfg : f ≫ g = 0} (hS : (ShortComplex.mk f g hfg).Exact) :
      Function.Exact (Preadditive.rightCompEndOp (𝟙_ C) f)
        (Preadditive.rightCompEndOp (𝟙_ C) g) := by
    obtain ⟨n, ⟨bX⟩⟩ := hX.exists_unitBasis
    obtain ⟨m, ⟨bY⟩⟩ := hY.exists_unitBasis
    exact bX.exact_rightCompEndOp hKf bY hS
  have hcomm {X Y : C} {φ : X ⟶ X} {ψ : Y ⟶ Y} {f : X ⟶ Y} (h : φ ≫ f = f ≫ ψ) :
      Preadditive.rightCompEndOp (𝟙_ C) f ∘ₗ Preadditive.rightCompEndOp (𝟙_ C) φ =
        Preadditive.rightCompEndOp (𝟙_ C) ψ ∘ₗ Preadditive.rightCompEndOp (𝟙_ C) f :=
    LinearMap.ext fun x ↦ by simp [h]
  have hsub {X : C} (hX : IsZero X) : Subsingleton (𝟙_ C ⟶ X) :=
    ⟨fun x y ↦ hX.eq_of_tgt x y⟩
  have := fun j ↦ hfin (hA j)
  have := fun j ↦ hfin (hB j)
  have := fun j ↦ hfin (hD j)
  have key := LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (k := (End (𝟙_ C))ᵐᵒᵖ) (A := fun j ↦ 𝟙_ C ⟶ A j) (B := fun j ↦ 𝟙_ C ⟶ B j)
    (D := fun j ↦ 𝟙_ C ⟶ D j) (fun j ↦ Preadditive.rightCompEndOp _ (φA j))
    (fun j ↦ Preadditive.rightCompEndOp _ (φB j)) (fun j ↦ Preadditive.rightCompEndOp _ (φD j))
    (fun j ↦ Preadditive.rightCompEndOp _ (u j)) (fun j ↦ Preadditive.rightCompEndOp _ (v j))
    (fun j ↦ Preadditive.rightCompEndOp _ (w j)) (fun j ↦ hcomm (hu j)) (fun j ↦ hcomm (hv j))
    (fun j ↦ hcomm (hw j)) (fun j ↦ hex (hA j) (hB j) (ex₁ j))
    (fun j ↦ hex (hB j) (hD j) (ex₂ j)) (fun j ↦ hex (hD j) (hA (j + 1)) (ex₃ j))
    (hbdd.imp fun a ↦ Exists.imp fun b hab j hj ↦
      ⟨hsub (hab j hj).1, hsub (hab j hj).2.1, hsub (hab j hj).2.2⟩)
  simp only [htr (hA _), htr (hB _), htr (hD _)] at key
  have hop (f : ℤ → End (𝟙_ C)) : MulOpposite.op (∑ᶠ j, f j) = ∑ᶠ j, MulOpposite.op (f j) :=
    (MulOpposite.opAddEquiv : End (𝟙_ C) ≃+ _).toAddMonoidHom.map_finsum_of_injective
      MulOpposite.op_injective f
  apply MulOpposite.op_injective
  simpa only [superTrace, MulOpposite.op_add, hop, MulOpposite.op_smul] using key

end CategoryTheory
