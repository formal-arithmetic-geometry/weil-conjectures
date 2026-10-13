module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.FiniteCoconeStationary

/-! Finite diagonal tails yield stationary limiting subobjects.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-limits).
-/

@[expose] public section

set_option linter.unusedVariables false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- Finite diagonal tails make the canonical cycle tower regular and admit limits.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-limits).

Proof: On each diagonal, the cocone equation and the two eventually
isomorphic structure maps make `Alpha` an isomorphism in a sufficiently
low range. The upper zero tail makes the relevant incoming images eventually
zero. Induction on the derived exact-couple recursion then shows that the
cycle subobjects are eventually constant; the same induction identifies the
boundary subobjects with eventual images of kernels of outgoing iterates.
Decreasing cycles and increasing boundaries therefore have stationary values,
which are their greatest lower and least upper bounds. Taking these values as
the two components of `L` gives a limiting subobject, and cycle stationarity
is exactly the regularity condition. -/
theorem finiteCocone_limits
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)))) :
    ∃ L : X.LimitSubobjects, X.IsRegular := by
  have hstat := finiteCocone_stationary X A hA
  let T := X.cycleBoundaryTower
  let R : ℤ → ℤ → ℕ := fun p q ↦ Classical.choose (hstat p q)
  have hr (p q : ℤ) : ∀ t : ℕ, R p q ≤ t →
      T.Z t p q = T.Z (R p q) p q ∧ T.B t p q = T.B (R p q) p q := by
    exact Classical.choose_spec (hstat p q)
  let Z : ∀ p q : ℤ, Subobject (X.E p q) := fun p q ↦ T.Z (R p q) p q
  let B : ∀ p q : ℤ, Subobject (X.E p q) := fun p q ↦ T.B (R p q) p q
  have hZ (p q : ℤ) (t : ℕ) (ht : R p q ≤ t) : T.Z t p q = Z p q := hr p q t ht |>.1
  have hB (p q : ℤ) (t : ℕ) (ht : R p q ≤ t) : T.B t p q = B p q := hr p q t ht |>.2
  have hreg : X.IsRegular := by
    intro p q
    exact ⟨R p q, fun t ht ↦ hZ p q t ht⟩
  let L : X.LimitSubobjects := {
    Z := Z
    B := B
    Z_glb := by
      intro p q
      refine ⟨?_, ?_⟩
      · rintro S ⟨t, rfl⟩
        by_cases ht : R p q ≤ t
        · exact le_of_eq (hZ p q t ht).symm
        · have hm : Antitone (fun k ↦ T.Z k p q) :=
            antitone_nat_of_succ_le (fun k ↦ T.Z_decreasing k p q)
          have htr : t ≤ R p q := by omega
          simpa [Z] using (hm htr)
      · intro S hS
        exact hS ⟨R p q, rfl⟩
    B_lub := by
      intro p q
      refine ⟨?_, ?_⟩
      · rintro S ⟨t, rfl⟩
        by_cases ht : R p q ≤ t
        · exact le_of_eq (hB p q t ht)
        · have hm : Monotone (fun k ↦ T.B k p q) :=
            monotone_nat_of_le_succ (fun k ↦ T.B_increasing k p q)
          have htr : t ≤ R p q := by omega
          change T.B t p q ≤ T.B (R p q) p q
          exact hm htr
      · intro S hS
        exact hS ⟨R p q, rfl⟩
  }
  exact ⟨L, hreg⟩

end CategoryTheory.BigradedExactCouple
