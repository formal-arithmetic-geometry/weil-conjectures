module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Algebra.Basic

/-!
# Graded-uniform Hom divisibility for finite near-projective modules

Source: Stacks Project, Local Cohomology, Tags 0GA6 and 0GAC (lemma-factor-hom),
and More on Algebra, Tags 0G92 and 0G93
(blueprint: lem-per-graded-near-projective-hom-divisibility).

The ideal-power quotients are written as `K^r / (K^n • ⊤)`, where the top submodule
is in `K^r`. Its denominator is exactly `K^(n+r)` inside `K^r`. Mathlib supplies
the quotient's canonical `R/K^n` action. The two helper maps are induced by inclusion
and multiplication on representatives, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u v z

namespace Ideal

variable {R : Type v} [CommRing R]

/-- The map `K^r/K^(n+r) → K^t/K^(n+t)` induced by inclusion when `t ≤ r`.
Source: Stacks Project, Tag 0GAC, the map following `φ`
(blueprint: lem-per-graded-near-projective-hom-divisibility). -/
noncomputable def homDivisibilityQuotientMap (K : Ideal R) (n r t : ℕ) (h : t ≤ r) :
    ((K ^ r : Ideal R) ⧸ (K ^ n • ⊤ : Submodule R (K ^ r : Ideal R))) →ₗ[R ⧸ K ^ n]
      ((K ^ t : Ideal R) ⧸ (K ^ n • ⊤ : Submodule R (K ^ t : Ideal R))) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (Submodule.mapQ _ _ (Submodule.inclusion (Ideal.pow_le_pow_right h))
      (Submodule.smul_top_le_comap_smul_top _ _))

/-- Multiplication by `a ∈ K^c`, from `K^w/K^(n+w)` to `K^t/K^(n+t)`,
where `t = c+w`. Source: Stacks Project, Tag 0GAC, the maps `a_i ψ_i`
(blueprint: lem-per-graded-near-projective-hom-divisibility). -/
noncomputable def homDivisibilityQuotientMul (K : Ideal R) (n c w t : ℕ)
    (h : t = c + w) (a : (K ^ c : Ideal R)) :
    ((K ^ w : Ideal R) ⧸ (K ^ n • ⊤ : Submodule R (K ^ w : Ideal R))) →ₗ[R ⧸ K ^ n]
      ((K ^ t : Ideal R) ⧸ (K ^ n • ⊤ : Submodule R (K ^ t : Ideal R))) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (Submodule.mapQ _ _
      (((LinearMap.mul R R a.1).domRestrict (K ^ w)).codRestrict (K ^ t)
        (fun b => by
          change a.1 * b.1 ∈ K ^ t
          rw [h, pow_add]
          exact Ideal.mul_mem_mul a.2 b.2))
      (Submodule.smul_top_le_comap_smul_top _ _))

/-- Graded-uniform divisibility of Hom from finite near-projective modules.
Source: Stacks Project, Tags 0GA6 and 0GAC, with the finite-free factorization
criterion of More on Algebra, Tags 0G92 and 0G93
(blueprint: lem-per-graded-near-projective-hom-divisibility).

Proof plan:
1. Use `lem-per-blowup-uniform-tensor-section-bound` to choose graded-invariant
   constants `d ≥ 1, q ≥ 0`, and take `D = d`. If `n = 0`, the quotient ring and
   module are zero and the empty sum works. Otherwise use its blowup thickening
   `Y_n`, line module `L_n`, and section `s_n`. Put `t = n-(D+1)c`, `w = n-(D+2)c`.
   The bounds give `w ≥ 0`, `t = w+c ≥ q`, and `n-2c ≥ q+(D-1)c`.
   By `lem-per-near-projective-dual-comparison`, the finite dual `N = Hom(M,A)`
   has the same factorization property. On `Y_n`, the comparison from the pullback
   of `N` to the dual of the pullback of `M` has kernel and cokernel killed by `s_n^c`.
2. Apply `lem-per-line-twist-double-annihilator-reverse` to obtain the reverse
   map from the dual at twist `n` to the pullback of `N` at twist `n-2c`.
   Pulling back `u` gives a section `σ` of the twisted dual; send it to `σ'` by
   the reverse map. Evaluation at each `z ∈ M` commutes with the comparison,
   since locally `(b ⊗ λ)(1 ⊗ z) = b λ(z)`, and the composite is `δ_(2c)`.
3. The tensor-section bound at `r = n-2c` shows that the image of `σ'` at twist
   `t` comes from `τ ∈ K^t ⊗ N`. Expand `K^t = K^c K^w` to write a finite sum
   `τ = Σ a_j τ_j`, with `a_j ∈ K^c`, `τ_j ∈ K^w ⊗ N`. For an expression
   `τ_j = Σ b_jl ⊗ λ_jl`, define `ψ_j(z) = Σ b_jl λ_jl(z)` modulo `K^(n+w)`.
   Lifts of the values of `λ_jl` differ by `K^n`, hence their products differ
   by `K^(n+w)`. Bilinearity makes the construction independent of the tensor
   expression and linear over `A`.
4. Evaluate the section identity and apply the comparison at twist `t`.
   Compatibility with decreasing twists identifies the left side with the
   image of `p u(z)` under `θ_(n,t)`, and the right with that of `Σ μ_(a_j) ψ_j(z)`.
   Since `t ≥ q`, `θ_(n,t)` is injective, proving the desired equality for every
   `z`. The bounds `0 ≤ t ≤ n` define `p`, and `t = w+c` makes each multiplication
   map well defined with precisely the displayed quotient-module actions.
-/
theorem exists_graded_nearProjective_hom_divisibility
    (R₀ : Type u) [CommRing R₀] [IsNoetherianRing R₀] (K₀ : Ideal R₀) :
    ∃ D q : ℕ, ∀ (R : Type v) [CommRing R] [IsNoetherianRing R] (K : Ideal R)
      (e : K.associatedGraded ≃+* K₀.associatedGraded),
      (∀ j : ℕ,
        Set.range (fun x : K.associatedGradedPiece j => e (DirectSum.of _ j x)) =
          Set.range (DirectSum.of (fun k : ℕ => K₀.associatedGradedPiece k) j)) →
      ∀ (n c : ℕ) (hcn : c ≤ n)
        (hb : max (q + (D + 1) * c) ((D + 2) * c) ≤ n)
        (hzero : D = 0 → q + 2 * c ≤ n)
        (M : Type z) [AddCommGroup M] [Module (R ⧸ K ^ n) M]
        [Module.Finite (R ⧸ K ^ n) M],
        (∀ a : (K ^ c : Ideal R), ∃ (r : ℕ)
          (f : M →ₗ[R ⧸ K ^ n] (Fin r → R ⧸ K ^ n))
          (g : (Fin r → R ⧸ K ^ n) →ₗ[R ⧸ K ^ n] M),
          ∀ x : M, g (f x) = Ideal.Quotient.mk (K ^ n) a.1 • x) →
        ∀ u : M →ₗ[R ⧸ K ^ n]
          ((K ^ n : Ideal R) ⧸ (K ^ n • ⊤ : Submodule R (K ^ n : Ideal R))),
        ∃ (m : ℕ) (a : Fin m → (K ^ c : Ideal R))
          (ψ : Fin m → M →ₗ[R ⧸ K ^ n]
            ((K ^ (n - (D + 2) * c) : Ideal R) ⧸
              (K ^ n • ⊤ : Submodule R (K ^ (n - (D + 2) * c) : Ideal R)))),
          (homDivisibilityQuotientMap K n n (n - (D + 1) * c) (Nat.sub_le _ _)).comp u =
            ∑ j : Fin m,
              (homDivisibilityQuotientMul K n c (n - (D + 2) * c)
                (n - (D + 1) * c) (by
                  have hn := (le_max_right (q + (D + 1) * c) ((D + 2) * c)).trans hb
                  simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul] at *
                  omega) (a j)).comp (ψ j) := by
  sorry

end Ideal
