module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-! # Contractibility of the power-set complex
Source: literature/stacks-project/sites-cohomology.tex, Tag 03AT
(blueprint: lem-weil-pbc-power-set-complex-contractible)
-/

@[expose] public section

open scoped BigOperators

namespace Algebra

universe u v

variable (A : Type u) [Ring A] (S : Type v)

/-- The free `A`-module on `(p+1)`-tuples in `S`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
abbrev powerSetComplexObject (p : ℕ) : Type (max u v) := (Fin (p + 1) → S) →₀ A

/-- Deletion of the `j`-th entry of a tuple.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
def powerSetComplexFace {p : ℕ} (j : Fin (p + 2))
    (x : Fin (p + 2) → S) : Fin (p + 1) → S :=
  fun i => x (Fin.succAbove j i)

/-- The alternating face differential on free modules on tuples.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexDifferential (p : ℕ) :
    powerSetComplexObject A S (p + 1) →ₗ[A] powerSetComplexObject A S p :=
  (Finsupp.lift _ _ _) (fun x =>
    ∑ j : Fin (p + 2),
      ((-1 : A) ^ (j : ℕ)) • Finsupp.single (powerSetComplexFace S (p := p) j x) 1)

/-- The augmentation sending each basis element to `1`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexAugmentation :
    powerSetComplexObject A S 0 →ₗ[A] A :=
  (Finsupp.lift _ _ _) (fun _ => 1)

/-- The contracting homotopy `[(s₀,…,sₚ)] ↦ [(s,s₀,…,sₚ)]` prefixing a chosen `s : S`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexHomotopy (s : S) (p : ℕ) :
    powerSetComplexObject A S p →ₗ[A] powerSetComplexObject A S (p + 1) :=
  Finsupp.lmapDomain A A (fun x : Fin (p + 1) → S => (Fin.cons s x : Fin (p + 2) → S))

/-- The degree `-1` part of the contracting homotopy, `A → C₀(S;A)`, `1 ↦ [s]`.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-power-set-complex-contractible). -/
noncomputable def powerSetComplexAugmentationHomotopy (s : S) :
    A →ₗ[A] powerSetComplexObject A S 0 :=
  Finsupp.lsingle (fun _ => s)

/-- The tuple complex `C_•(S;A)` with `d ∘ d = 0` and `ε ∘ d = 0`; it is zero when `S` is
empty; for nonempty `S` the augmented complex `⋯ → C₁ → C₀ → A → 0` is exact in every
degree (at `C_{p+1}`, at `C₀`, and at `A`: `ε` is surjective), so `H_p = 0` for `p > 0` and
`ε` induces `H₀ ≅ A`; and for every `s : S` the prefixing maps form a contracting homotopy of
the augmented complex.
Source: Stacks Project, Lemma Tag 03AT, last paragraph of the proof
(blueprint: lem-weil-pbc-power-set-complex-contractible).
Proof: (1) `d ∘ d = 0` and `ε ∘ d = 0` on basis tuples by the sign cancellation of the
two deletion orders, and `ε(d[(s₀,s₁)]) = 1 - 1 = 0`. (2) If `S` is empty there are no
tuples, so every `C_p` is zero. (3) For `s : S`, on basis elements
`d(h x) = x - h(d x)` in positive degrees, `d(h[s₀]) + h(ε[s₀]) = [s₀]` and `ε(h 1) = 1`.
(4) A contracting homotopy of the augmented complex gives its exactness in every degree
(lem-weil-pbc-contractible-complex-acyclic). -/
theorem powerSetComplex_contractible :
    (∀ p : ℕ,
      (powerSetComplexDifferential A S p).comp
          (powerSetComplexDifferential A S (p + 1)) = 0) ∧
    (powerSetComplexAugmentation A S).comp
          (powerSetComplexDifferential A S 0) = 0 ∧
    (IsEmpty S → ∀ p : ℕ, Subsingleton (powerSetComplexObject A S p)) ∧
    (Nonempty S →
      (∀ p : ℕ,
        LinearMap.range (powerSetComplexDifferential A S (p + 1)) =
          LinearMap.ker (powerSetComplexDifferential A S p)) ∧
      LinearMap.range (powerSetComplexDifferential A S 0) =
        LinearMap.ker (powerSetComplexAugmentation A S) ∧
      LinearMap.range (powerSetComplexAugmentation A S) = ⊤) ∧
    (∀ s : S,
      (powerSetComplexAugmentation A S).comp
          (powerSetComplexAugmentationHomotopy A S s) = LinearMap.id ∧
      (powerSetComplexDifferential A S 0).comp (powerSetComplexHomotopy A S s 0) +
          (powerSetComplexAugmentationHomotopy A S s).comp
            (powerSetComplexAugmentation A S) = LinearMap.id ∧
      ∀ p : ℕ,
        (powerSetComplexDifferential A S (p + 1)).comp
            (powerSetComplexHomotopy A S s (p + 1)) +
          (powerSetComplexHomotopy A S s p).comp
            (powerSetComplexDifferential A S p) = LinearMap.id) := by
  sorry

end Algebra
