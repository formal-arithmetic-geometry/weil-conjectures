import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.HasLimits
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
universe u
/-! # Sections over a quasi-compact open in an affine scheme
Source: literature/stacks-project/properties.tex, Lemma 01PM
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open-in-affine)
-/
/-- The affine sections calculation of Properties, Lemma 01PM.
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open-in-affine)
-/
theorem sections_over_quasiCompactOpen_of_affine
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (I : Ideal A) (hIfg : I.FG)
    (D : (Spec (CommRingCat.of A)).Opens)
    (hD : ∀ (p : PrimeSpectrum A), p ∈ D ↔ ¬ ∀ a : A, a ∈ I → a ∈ p.asIdeal)
    (N : ℕ → Submodule A M)
    (hN : ∀ n x, x ∈ N n ↔ ∀ a : A, a ∈ I ^ n → a • x = 0) :
    ∃ c : (Σ n : ℕ,
      ((ModuleCat.of A (I ^ n : Ideal A)) ⟶ ModuleCat.of A M)) →
        Γ(tilde (ModuleCat.of A M), D),
      ∃ c' : (Σ n : ℕ,
        ((ModuleCat.of A (I ^ n : Ideal A)) ⟶ ModuleCat.of A (M ⧸ N n))) →
        Γ(tilde (ModuleCat.of A M), D),
      Function.Injective c ∧ Function.Bijective c' ∧
      ((∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) →
        Function.Bijective c) := by sorry
end AlgebraicGeometry
