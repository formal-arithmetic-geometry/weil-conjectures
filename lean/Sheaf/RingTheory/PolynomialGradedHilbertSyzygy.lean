module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.ProjectiveResolutionKernelProjective

/-!
# Graded Hilbert syzygy over a polynomial ring

Source: Stacks Project, Algebra, Tags 00OQ and 0EKB; the finite shifted-free enhancement
extracted in the DAG (blueprint: lem-sfb-polynomial-graded-hilbert-syzygy).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A finite integer-graded module over a polynomial ring in `m` variables admits a
finite graded free resolution in homological degrees `0` through `m`.

Source: Stacks Project, Algebra, Tag 00OQ (global dimension of a polynomial ring),
Tag 0EKB (graded Nakayama), with the graded enhancement proved in the node
(blueprint: lem-sfb-polynomial-graded-hilbert-syzygy).

The polynomial grading is `homogeneousSubmodule`, extended by zero in negative degrees.
An internal grading compatible with homogeneous scalar multiplication suffices: constants
then preserve every component, so the components are also vector subspaces over `k`.
The finite set at stage `i` is `Fin (r i)`. A homogeneous basis vector of degree `-d i a`
identifies its summand with `S(d i a)`, since `S(d)_b = S_{d+b}`. Thus the homogeneous
basis describes precisely the direct sum of shifts, without choosing new shift definitions.
The map `f j hj` goes from `F_(j+1)` to `F_j`; `q` is the augmentation. The injectivity
clause with `j + 1 = m` specifies the left endpoint when `m > 0`. For `m = 0`, the
left endpoint is `q` itself, and its injectivity and surjectivity make it an isomorphism.

Proof:
1. Replace finite generators of a graded module `N` by all their homogeneous components.
   They still generate: their span contains each original generator. For generator degrees
   `e a`, map the basis vector of `S(-e a)` to that generator. This gives a degree-preserving
   finite free surjection, with the shift sign as in Tag 0EKB(4).
2. Start with `K_0 = M` and repeat these covers `m` times, taking `K_(j+1)` to be the
   kernel of the cover of `K_j`. Kernels are graded by uniqueness of homogeneous
   decomposition. Polynomial regularity gives Noetherianity
   (lem-weil-pbc-polynomial-ring-field-regular-ring), so each kernel is finite
   (lem-weil-pbc-noetherian-submodule-finite). The free modules are projective
   (def-weil-pbc-projective-module). This constructs an exact partial resolution.
3. The global-dimension bound (lem-sfb-polynomial-projective-dimension-bound) and the
   terminal-kernel criterion (lem-weil-pbc-projective-resolution-kernel-projective) make
   `K_m` projective. If `m = 0`, the criterion makes `K_0 = M` projective directly.
4. Apply lem-sfb-connected-graded-projective-free to `K_m` over the polynomial ring,
   whose nonnegative grading has degree-zero part `k`. Its finite homogeneous basis
   identifies `K_m` with a finite sum of shifts. Splice this isomorphism with its kernel
   inclusion. This gives the injective left map, all image-kernel equalities, and the
   surjective augmentation. Negate the basis degrees to obtain the shift parameters.
5. If `M = 0`, take every basis empty. Once any kernel is zero, all later covers may
   be zero. Arbitrary integer basis degrees and `m = 0` require no additional hypotheses. -/
theorem exists_graded_free_resolution_finite {k : Type u} [Field k] (m : ℕ)
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin m) k) M]
    [Module.Finite (MvPolynomial (Fin m) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin m) k) (x : M),
      s ∈ homogeneousSubmodule (Fin m) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (F : Fin (m + 1) → ModuleCat.{u} (MvPolynomial (Fin m) k))
      (𝒢 : ∀ i : Fin (m + 1), ℤ → AddSubgroup (F i)) (r : Fin (m + 1) → ℕ)
      (d : ∀ i : Fin (m + 1), Fin (r i) → ℤ)
      (b : ∀ i : Fin (m + 1), Module.Basis (Fin (r i)) (MvPolynomial (Fin m) k) (F i))
      (f : ∀ (j : ℕ) (hj : j < m),
        F ⟨j + 1, Nat.succ_lt_succ hj⟩ →ₗ[MvPolynomial (Fin m) k]
          F ⟨j, Nat.lt_succ_of_lt hj⟩)
      (q : F 0 →ₗ[MvPolynomial (Fin m) k] M),
      (∀ i : Fin (m + 1), DirectSum.IsInternal (𝒢 i)) ∧
      (∀ (i : Fin (m + 1)) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin m) k) (x : F i),
        s ∈ homogeneousSubmodule (Fin m) k n → x ∈ 𝒢 i j →
          s • x ∈ 𝒢 i ((n : ℤ) + j)) ∧
      (∀ (i : Fin (m + 1)) (a : Fin (r i)), b i a ∈ 𝒢 i (-(d i a))) ∧
      (∀ (i : ℕ) (hi : i < m) (j : ℤ)
        (x : F ⟨i + 1, Nat.succ_lt_succ hi⟩),
        x ∈ 𝒢 ⟨i + 1, Nat.succ_lt_succ hi⟩ j →
          f i hi x ∈ 𝒢 ⟨i, Nat.lt_succ_of_lt hi⟩ j) ∧
      (∀ (j : ℤ) (x : F 0), x ∈ 𝒢 0 j → q x ∈ ℳ j) ∧
      (m = 0 → Function.Injective q) ∧
      (∀ (j : ℕ) (hj : j < m), j + 1 = m → Function.Injective (f j hj)) ∧
      (∀ h : 0 < m, LinearMap.range (f 0 h) = LinearMap.ker q) ∧
      (∀ (j : ℕ) (hj : j + 1 < m),
        LinearMap.range (f (j + 1) hj) = LinearMap.ker (f j (Nat.lt_of_succ_lt hj))) ∧
      Function.Surjective q := by
  sorry

end MvPolynomial
