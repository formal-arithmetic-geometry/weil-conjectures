module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Recursive extension of a comparison map along an exact resolution.
Source: literature/stacks-project/algebra.tex, Tag 00LS.
(blueprint: lem-weil-pbc-free-complex-extend-family).
-/

@[expose] public section

universe u

open CategoryTheory

/-- Given the degree-zero lift, projectivity and exactness recursively produce
all higher components of the chain map.  The theorem packages the dependent
infinite recursion from Tag 00LS into one strictly lower intermediate claim.
Source: Algebra, Tag 00LS, proof of lemma-compare-resolutions (1), lines 17527--17535.
(blueprint: lem-weil-pbc-free-complex-extend-family). -/
theorem free_complex_extend_family
    (R : Type u) [CommRing R]
    (N : ModuleCat R) (N' : ℕ → ModuleCat R)
    (d : ∀ i : ℕ, N' (i + 1) ⟶ N' i)
    (η : N' 0 ⟶ N)
    (hd0 : d 0 ≫ η = 0)
    (hd : ∀ i : ℕ, d (i + 1) ≫ d i = 0)
    (hex0 : (ShortComplex.mk (d 0) η hd0).Exact)
    (hex : ∀ i : ℕ, (ShortComplex.mk (d (i + 1)) (d i) (hd i)).Exact)
    (F : ℕ → ModuleCat R)
    (δ : ∀ i : ℕ, F (i + 1) ⟶ F i)
    (hδ : ∀ i : ℕ, δ (i + 1) ≫ δ i = 0)
    (hfree : ∀ i : ℕ, Module.Free R (F i))
    (a₀ : F 0 ⟶ N' 0) :
    ∃ α : ∀ i : ℕ, F i ⟶ N' i,
      α 0 = a₀ ∧ (∀ i : ℕ, α (i + 1) ≫ d i = δ i ≫ α i) := by
  sorry
