/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Finite-rank correction of a square-zero-valued field derivation

Source: Stacks Project, Tag 07FG, differential-basis and Jacobi--Zariski paragraphs.
(blueprint: lem-weil-pbc-finite-rank-defect-derivation)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- A derivation of `k` into an ideal annihilated by the residue kernel extends to `K`
up to an error contained in the `k`-span of finitely many elements of the ideal.
No coefficient subfield or generated subring is involved in this assertion.

Source: Stacks Project, Tag 07FG, from the choice of the differential basis to the
finite family of values of the corrected derivation.
(blueprint: lem-weil-pbc-finite-rank-defect-derivation)

Proof:
1. Use the section to act on `I` by `K`. Since `(ker r) * I = 0`, multiplication
   by any lift of a residue scalar gives the same action. Compatibility of `r`
   with `k` identifies its restricted action with the given `k`-action. Thus
   `theta`, with the displayed product rule, is an absolute derivation into `I`.
   It kills the prime field (integers by additivity, and inverses by Leibniz).
2. Choose a basis of differentials `dy_j` of `Omega(k/F_p)` from its spanning
   family. Extend scalars to `K`. Jacobi--Zariski exactness identifies the kernel
   of the map to `Omega(K/F_p)` with the image of `H1Cotangent k K`. Finite
   dimensionality implies this kernel is supported on a finite subset `J0` of
   the basis. Consequently the images of `dy_j` outside `J0` are independent.
3. Extend those images to a basis of `Omega(K/F_p)`. Define a `K`-linear map to
   `I` taking these images to `theta(y_j)` and taking the additional basis
   vectors to zero. Compose with the universal derivation to obtain `D`.
   The difference `theta - D|k` factors through the projection onto the
   `k`-span of `dy_j` for `j` in `J0`. Let `f` be the finite image of those
   basis elements under this difference. Every corrected value is in its
   `k`-span; every generator belongs to `I`. The zero ideal gives `D = 0`
   and the empty family, so no nonzero-module assumption is necessary. -/
theorem exists_finite_rank_defect_derivation
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ]
    (r : Λ →+* K) (hcomm : r.comp (algebraMap k Λ) = algebraMap k K)
    (I : Ideal Λ) (hI : I ≤ RingHom.ker r) (hkill : RingHom.ker r * I = ⊥)
    (σ0 : K →+* Λ) (hσ0 : r.comp σ0 = RingHom.id K)
    (theta : k →+ Λ) (htheta : ∀ a : k, theta a ∈ I)
    (htheta_one : theta 1 = 0)
    (htheta_mul : ∀ a b : k,
      theta (a * b) = algebraMap k Λ a * theta b + algebraMap k Λ b * theta a)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) :
    ∃ (D : K →+ Λ) (f : Finset Λ),
      D 1 = 0 ∧
      (∀ x y : K, D (x * y) = σ0 x * D y + σ0 y * D x) ∧
      (∀ x : K, D x ∈ I) ∧
      (f : Set Λ) ⊆ I ∧
      (∀ a : k, theta a - D (algebraMap k K a) ∈
        Submodule.span k (f : Set Λ)) := by sorry

end Algebra
