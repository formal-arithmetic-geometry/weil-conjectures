module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Corepresenting Hom bijections from compatible cokernel presentations

Source: Stacks Project, Homology, Tag 0793, `lemma-partially-defined-adjoint`,
final paragraph, the three displayed Hom identifications
(blueprint: lem-trf-cokernel-corepresenting-bijection).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

/-- Compatible zero-preserving natural Hom bijections for two objects descend to the
cokernels of compatible arrows. The resulting family is uniquely characterized by its
composite with the given cokernel projection, has the stated inverse factorization, and
is natural in the target.

Source: Stacks Project, Homology, Tag 0793, `lemma-partially-defined-adjoint`,
final paragraph (blueprint: lem-trf-cokernel-corepresenting-bijection).

Proof plan:
1. Given `v : C ⟶ X`, compatibility and zero preservation give
   `d ≫ θ₁ X (c ≫ v) = θ₂ X (D ≫ c ≫ v) = 0`. The universal property of the
   cokernel `q` gives a unique `b` with `q ≫ b = θ₁ X (c ≫ v)`; define `ψ X v = b`.
   This uses `def-sp-abelian` and `def-weil-pbc-category-colimit`.
2. Conversely, for `b : B ⟶ R.obj X`, set `a = (θ₁ X).symm (q ≫ b)`.
   Compatibility gives `θ₂ X (D ≫ a) = d ≫ q ≫ b = 0 = θ₂ X 0`.
   Injectivity of `θ₂ X` implies `D ≫ a = 0`. The cokernel property of `c` gives
   the unique `v` with `c ≫ v = a` (`def-weil-pbc-category-colimit`).
3. The two constructions are inverse: their composites with `c`, respectively `q`,
   agree with those of the identity, so uniqueness of cokernel factorizations proves
   both inverse identities (`def-weil-pbc-category-colimit`).
4. For `u : X ⟶ X'`, naturality of `θ₁` makes the composites with `q` of
   `ψ X' (v ≫ u)` and `ψ X v ≫ R.map u` equal. Cokernel uniqueness gives naturality.
   Any competing family with the normalization has the same composites with `q`
   pointwise, hence is equal to `ψ` (`def-weil-pbc-category-colimit`). -/
theorem exists_cokernel_corepresenting_bijection
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {𝓑 : Type u₂} [Category.{v₂} 𝓑] [Abelian 𝓑]
    (R : A ⥤ 𝓑) {P₂ P₁ B : 𝓑} (d : P₂ ⟶ P₁) (q : P₁ ⟶ B)
    (hdq : d ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q hdq))
    (L₁ L₂ : A)
    (θ₁ : ∀ X : A, (L₁ ⟶ X) ≃ (P₁ ⟶ R.obj X))
    (θ₂ : ∀ X : A, (L₂ ⟶ X) ≃ (P₂ ⟶ R.obj X))
    (hθ₁ : ∀ (X X' : A) (u : X ⟶ X') (a : L₁ ⟶ X),
      θ₁ X' (a ≫ u) = θ₁ X a ≫ R.map u)
    (hθ₂ : ∀ (X X' : A) (u : X ⟶ X') (a : L₂ ⟶ X),
      θ₂ X' (a ≫ u) = θ₂ X a ≫ R.map u)
    (hθ₁_zero : ∀ X : A, θ₁ X 0 = 0)
    (hθ₂_zero : ∀ X : A, θ₂ X 0 = 0)
    (D : L₂ ⟶ L₁)
    (hD : ∀ (X : A) (a : L₁ ⟶ X), θ₂ X (D ≫ a) = d ≫ θ₁ X a)
    {C : A} (c : L₁ ⟶ C) (hDc : D ≫ c = 0)
    (hc : IsColimit (CokernelCofork.ofπ c hDc)) :
    ∃ ψ : ∀ X : A, (C ⟶ X) ≃ (B ⟶ R.obj X),
      (∀ (X : A) (v : C ⟶ X), q ≫ ψ X v = θ₁ X (c ≫ v)) ∧
      (∀ ψ' : ∀ X : A, (C ⟶ X) ≃ (B ⟶ R.obj X),
        (∀ (X : A) (v : C ⟶ X), q ≫ ψ' X v = θ₁ X (c ≫ v)) → ψ' = ψ) ∧
      (∀ (X : A) (b : B ⟶ R.obj X),
        c ≫ (ψ X).symm b = (θ₁ X).symm (q ≫ b) ∧
        ∀ v : C ⟶ X, c ≫ v = (θ₁ X).symm (q ≫ b) → v = (ψ X).symm b) ∧
      (∀ (X X' : A) (u : X ⟶ X') (v : C ⟶ X),
        ψ X' (v ≫ u) = ψ X v ≫ R.map u) := by
  sorry

end CategoryTheory
