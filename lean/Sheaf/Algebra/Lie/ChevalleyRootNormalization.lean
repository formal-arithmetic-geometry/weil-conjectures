module

public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Normalizing a prescribed rational simple-root pinning

Source: Milne, Algebraic Groups (2017), Section 23h, pp. 508–509, Theorem 23.71
(blueprint: lem-sfb-chevalley-root-normalization).

The roots and coroots are a Mathlib root pairing with the evaluation pairing on `H`.
Root spaces are ordinary simultaneous eigenspaces `LieModule.weightSpace`, rather than
Mathlib's generalized root spaces. The conclusion includes the entire integral bracket table.
-/

@[expose] public section

universe u v

open Module

namespace LieAlgebra

open Classical in
/-- A prescribed rational pinning extends to normalized root vectors and a Chevalley basis.
Source: Milne, Algebraic Groups (2017), Section 23h, pp. 508–509, Theorem 23.71
(blueprint: lem-sfb-chevalley-root-normalization).

Proof plan:
1. By `lem-sfb-root-base-rational-integral-spans`, the simple coroots form a basis of `H`,
   every coroot has integral simple-coroot coordinates, and the root-side base extends to a
   Mathlib root-pairing base. By `lem-sfb-rational-opposition-involution`, there is a rational
   involution `θ`, negative on `H`, normalizing the prescribed simple-root triples.
2. Let `Q(α)` assert the existence of a rational root vector `z` with
   `[z, -θ(z)] = h_α`. The simple-root cases are prescribed. Negation sends `z` to `-θ(z)`.
   In the additive step, `lem-sfb-opposition-root-bracket-norm` says that `[z, x_δ]` has
   squared norm `(p+1)^2 h_(α+δ)`, so division by `p+1` gives the required normalized vector.
   Jacobi gives its weight. Apply `lem-sfb-root-base-additive-induction` to obtain all roots.
3. Choose normalized vectors for the positive roots, retaining the prescribed simple ones,
   and put `e_(-α) = -θ(e_α)`. The sign-coherent coordinates partition the roots into positive
   and negative ones. Skew-symmetry and `h_(-α) = -h_α` give normalization for both signs.
4. A bracket of root vectors whose weights sum to a root is a rational multiple `N` of its
   chosen vector. Apply `lem-sfb-opposition-root-bracket-norm` and cancel the nonzero coroot
   to get `N^2 = (p+1)^2`, hence `N = ±(p+1)` over the rationals.
5. Jacobi and the root decomposition give zero brackets when the sum is neither a root nor
   zero. The simple coroot basis together with one nonzero vector per one-dimensional root
   space gives a basis of the whole algebra. Root-coroot pairings and all simple-coroot
   coordinates are integral, so every remaining bracket coefficient is integral. For an
   empty simple base, its spanning property gives `H = 0`, the root system is empty, and
   the root decomposition gives the zero algebra and its empty basis. -/
theorem exists_chevalley_basis_of_pinning
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [IsLieAbelian H]
    (hmax : ∀ K : LieSubalgebra ℚ L, H ≤ K → IsLieAbelian K → K = H)
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (f : Dual ℚ H) (h : H), P.toLinearMap f h = f h)
    (hdecomp : DirectSum.IsInternal
      (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
        (fun i : I ↦ (LieModule.weightSpace L (P.root i)).toSubmodule)))
    (hdim : ∀ i : I, Module.finrank ℚ (LieModule.weightSpace L (P.root i)) = 1)
    (hcoroot : ∀ i : I, (P.coroot i : L) ∈ Submodule.span ℚ
      {z : L | ∃ a ∈ LieModule.weightSpace L (P.root i),
        ∃ b ∈ LieModule.weightSpace L (-P.root i), ⁅a, b⁆ = z})
    (Δ : Set I) (b : Module.Basis Δ ℚ (Dual ℚ H))
    (hb : ∀ i : Δ, b i = P.root i)
    (hsign : ∀ i : I,
      P.root i ∈ AddSubmonoid.closure (P.root '' Δ) ∨
        -P.root i ∈ AddSubmonoid.closure (P.root '' Δ))
    (x : Δ → L) (hx : ∀ i : Δ, x i ∈ LieModule.weightSpace L (P.root i))
    (hxne : ∀ i : Δ, x i ≠ 0) :
    ∃ e : I → L,
      (∀ i : I, e i ∈ LieModule.weightSpace L (P.root i) ∧ e i ≠ 0) ∧
      (∀ i : Δ, e i = x i) ∧
      (∀ i : I, ⁅e i, e (P.reflectionPerm i i)⁆ = (P.coroot i : L)) ∧
      (∀ i j k : I, P.root i + P.root j = P.root k →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ⁅e i, e j⁆ = ((ε : ℚ) * (P.chainBotCoeff i j + 1)) • e k) ∧
      (∀ i j : I, P.root i + P.root j ∉ Set.range P.root →
        P.root i + P.root j ≠ 0 → ⁅e i, e j⁆ = 0) ∧
      ∃ B : Module.Basis (Δ ⊕ I) ℚ L,
        (∀ i : Δ, B (Sum.inl i) = (P.coroot i : L)) ∧
        (∀ i : I, B (Sum.inr i) = e i) ∧
        ∀ i j k : Δ ⊕ I, ∃ n : ℤ, B.repr ⁅B i, B j⁆ k = (n : ℚ) := by
  sorry

end LieAlgebra
