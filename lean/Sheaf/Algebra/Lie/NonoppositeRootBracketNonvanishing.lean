module

public import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Sl2

/-!
# Nonvanishing of brackets in nonopposite root spaces

Source: Milne, Algebraic Groups (2017), Section 23h, p. 503, and Theorem 23.71,
pp. 508–509 (blueprint: lem-sfb-nonopposite-root-bracket-nonvanishing).

The general-field root-string argument below is the agent-formulated local prerequisite
recorded in the DAG. Ordinary root spaces use `LieModule.weightSpace`; diagonalizability
over the given field means that the eigenspaces of each adjoint endomorphism span `L`.
-/

@[expose] public section

universe u v

namespace LieAlgebra

/-- Any two nonzero root vectors have nonzero bracket when their sum is a nonzero root.
Source: Milne, Algebraic Groups (2017), Section 23h, p. 503, and Theorem 23.71,
pp. 508–509 (blueprint: lem-sfb-nonopposite-root-bracket-nonvanishing).

Proof plan (the agent-formulated general-field argument recorded in the node):
1. Apply `lem-sfb-killing-cartan-rank-one-spaces`, since diagonalizability implies
   triangularizability. Ordinary and generalized root spaces agree: ordinary eigenvectors
   are generalized ones, and the cited lemma gives the converse. The nonzero root spaces
   are one-dimensional. Obtain a triple `(c, u, v)` with `α(c) = 2`, and rescale it so that
   its raising vector is the prescribed `x`: if `x = a • u`, put `f = a⁻¹ • v`.
   Then `[x,f] = c`, `[c,x] = 2x`, `[c,f] = -2f`, and `c ≠ 0`.
2. Set `E = ad(x)` and `F = ad(f)`. Jacobi (`def-wf-lie-algebra`) gives
   `E(L_γ) ⊆ L_(γ+α)` and `F(L_γ) ⊆ L_(γ-α)`.
   By `lem-sfb-nilpotent-module-generalized-weight-decomposition` only finitely many
   weights occur. The weights `γ + jα` are distinct in characteristic zero, since `α ≠ 0`.
   Consequently the raising sequence of any weight vector eventually vanishes.
3. Suppose `Ey = 0`. Since `[c,y] = β(c)y`, the primitive-vector theorem
   `lem-sfb-sl2-primitive-lowering-string` supplies a natural number `m` with `β(c) = m`.
4. Choose nonzero `z ∈ L_(α+β)` and its last nonzero raising vector `w = E^r z`.
   It has weight `β + (r+1)α` and highest weight `N = m + 2r + 2`.
   Apply `lem-sfb-sl2-primitive-lowering-string` again. It gives nonzero `F^(r+1)w`
   and `F^r w`, and `E F^(r+1)w = (r+1)(m+r+2) F^r w ≠ 0`.
   Both integer factors are positive and thus nonzero in the characteristic-zero field.
5. The lowering inclusion puts `F^(r+1)w` in the one-dimensional space `L_β`.
   Thus it is a scalar multiple of `y`, so its image under `E` vanishes by step 3,
   contradicting step 4. This proves the conclusion for every prescribed nonzero `x,y`. -/
theorem lie_ne_zero_of_nonopposite_root_vectors
    (K : Type u) [Field K] [CharZero K]
    (L : Type v) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (hdiag : ∀ h : H, (⨆ μ : K, (ad K L (h : L)).eigenspace μ) = ⊤)
    (α β : Module.Dual K H) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α + β ≠ 0)
    (hrootα : LieModule.weightSpace L (α : H → K) ≠ ⊥)
    (hrootβ : LieModule.weightSpace L (β : H → K) ≠ ⊥)
    (hrootαβ : LieModule.weightSpace L ((α + β : Module.Dual K H) : H → K) ≠ ⊥)
    (x y : L) (hx : x ∈ LieModule.weightSpace L (α : H → K))
    (hy : y ∈ LieModule.weightSpace L (β : H → K)) (hxne : x ≠ 0) (hyne : y ≠ 0) :
    ⁅x, y⁆ ≠ 0 := by
  sorry

end LieAlgebra
