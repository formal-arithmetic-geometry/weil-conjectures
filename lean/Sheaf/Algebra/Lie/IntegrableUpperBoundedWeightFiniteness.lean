module

public import Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition

/-!
# Finiteness of upper bounded integrable rational weight modules

Source: Milne, Algebraic Groups (2017), Section 23h, printed pp.508 and 511,
highest-weight background; the general criterion is the agent argument recorded in the DAG
(blueprint: lem-sfb-integrable-upper-bounded-weight-finiteness).

Weight spaces are ordinary simultaneous eigenspaces. The ambient representation is arbitrary;
only its individual weight spaces are assumed finite-dimensional.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace LieAlgebra

open Classical in
/-- An integrable rational weight module with finite-dimensional weight spaces and support
in finitely many upper cones has finite support and is finite-dimensional.

Source: Milne, Algebraic Groups (2017), Section 23h, printed pp.508 and 511,
highest-weight background; agent generalization of the integrable highest-weight argument
(blueprint: lem-sfb-integrable-upper-bounded-weight-finiteness).

Proof plan:
1. If `A` is empty, the support is empty and the internal direct sum makes `M` zero.
   In rank zero the dual of `H` is zero, so there is only the finite-dimensional zero weight.
2. Form the semidirect Lie algebra `g ⋉ M`, with bracket
   `[(x,u),(y,v)] = ([x,y], x v - y u)`. The representation identity gives Jacobi;
   `0 ⊕ M` is an abelian ideal and its Cartan weights are those of `M`.
3. The root-decomposition theorem gives normalized rank-one triples and nilpotence of
   the adjoint root operators on `g`. Together with local nilpotence on `M`, this gives
   local nilpotence on the semidirect algebra. Apply
   `lem-sfb-integrable-sl2-reflection-automorphism`. Its exponential factors preserve
   `0 ⊕ M`, so their restriction identifies the spaces of weights `μ` and
   `μ - μ (c i) • i`. The support is invariant under each simple reflection.
4. Let `W` be the group of simple reflections. The root-decomposition theorem makes
   it finite; put `d = |W|`. Define `ℓ` on the simple-root basis by `ℓ(αᵢ) = 1` and
   `C = max ({0} ∪ ℓ(A))`. Upper boundedness gives `ℓ(ν) ≤ C` on every weight.
5. The functional `B(x) = ∑ w ∈ W, ℓ(w x)` is invariant under every simple reflection.
   Since the reflection negates its simple root, `B` vanishes on each basis element,
   hence identically. Summing over the orbit of a weight gives `ℓ(μ) ≥ -(d-1)C`.
6. Write `μ = η - ∑ nᵢ αᵢ` with `η ∈ A` and natural `nᵢ`. The two bounds imply
   `∑ nᵢ ≤ dC`. Choose a natural bound `N ≥ dC`; all coefficients lie in `{0,…,N}`.
   The support is contained in the image of the finite set `A × {0,…,N}^Δ`.
7. Choose a finite basis in each nonzero weight space. Their finite union spans `M`
   by the internal direct sum, proving the second conclusion.

The coroots `c` are specified by their bracket-line membership and evaluation two, exactly
as in `exists_splitSemisimple_rootDecomposition`; no choice of a different pairing is made. -/
theorem finite_weights_and_finiteDimensional_of_integrable_upperBounded
    (g : Type u) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    [HasTrivialRadical ℚ g] (H : LieSubalgebra ℚ g) [IsLieAbelian H]
    (hmax : ∀ B : LieSubalgebra ℚ g, H ≤ B → IsLieAbelian B → B = H)
    (hsplit : ∀ h : H, (⨆ a : ℚ, (ad ℚ g (h : g)).eigenspace a) = ⊤)
    (R : Set (Module.Dual ℚ H))
    (hR : ∀ α : Module.Dual ℚ H, α ∈ R ↔
      α ≠ 0 ∧ LieModule.weightSpace g (α : H → ℚ) ≠ ⊥)
    (c : R → H)
    (hc : ∀ α : R,
      (c α : g) ∈ Submodule.span ℚ {z : g | ∃ x y : g,
        x ∈ LieModule.weightSpace g (α.1 : H → ℚ) ∧
        y ∈ LieModule.weightSpace g ((-α.1) : H → ℚ) ∧ ⁅x, y⁆ = z} ∧
      α.1 (c α) = 2)
    (Δ : Finset R) (b : Module.Basis Δ ℚ (Module.Dual ℚ H))
    (hb : ∀ i : Δ, b i = i.1.1)
    (hcoords : ∀ α : R,
      (∃ n : Δ → ℕ, α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1) ∨
      (∃ n : Δ → ℕ, -α.1 = ∑ i : Δ, (n i : ℚ) • i.1.1))
    (e f : Δ → g)
    (he : ∀ i : Δ, e i ∈ LieModule.weightSpace g (i.1.1 : H → ℚ) ∧ e i ≠ 0)
    (hf : ∀ i : Δ, f i ∈ LieModule.weightSpace g ((-i.1.1) : H → ℚ) ∧ f i ≠ 0)
    (hef : ∀ i : Δ, ⁅e i, f i⁆ = (c i.1 : g))
    (M : Type v) [AddCommGroup M] [Module ℚ M] [LieRingModule g M] [LieModule ℚ g M]
    (hdecomp : DirectSum.IsInternal (fun μ : Module.Dual ℚ H ↦
      (LieModule.weightSpace M (μ : H → ℚ)).toSubmodule))
    (hfinite : ∀ μ : Module.Dual ℚ H,
      FiniteDimensional ℚ (LieModule.weightSpace M (μ : H → ℚ)))
    (A : Finset (Module.Dual ℚ H))
    (hupper : ∀ μ : Module.Dual ℚ H, LieModule.weightSpace M (μ : H → ℚ) ≠ ⊥ →
      ∃ η ∈ A, ∃ n : Δ → ℕ, μ = η - ∑ i : Δ, (n i : ℚ) • i.1.1)
    (he_nil : ∀ (i : Δ) (m : M), ∃ n : ℕ, 0 < n ∧
      (LieModule.toEnd ℚ g M (e i) ^ n) m = 0)
    (hf_nil : ∀ (i : Δ) (m : M), ∃ n : ℕ, 0 < n ∧
      (LieModule.toEnd ℚ g M (f i) ^ n) m = 0) :
    {μ : Module.Dual ℚ H | LieModule.weightSpace M (μ : H → ℚ) ≠ ⊥}.Finite ∧
      FiniteDimensional ℚ M := by
  sorry

end LieAlgebra
