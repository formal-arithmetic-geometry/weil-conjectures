/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite image of prime-to-ell linear monodromy

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, pp. 2–3,
with the agent corollary using principal congruence subgroups
(blueprint: lem-sfb-prime-to-ell-linear-image-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Padic

/-- A jointly continuous finite-dimensional representation over a finite p-adic extension
of a profinite group whose finite continuous quotients have order prime to `l` has finite
image of order prime to `l`. Open normal subgroups encode those quotients. The topology
of `E` is the spectral-norm topology, and `M` carries its usual module topology.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, pp. 2–3;
agent corollary via the filtration of principal congruence subgroups
(blueprint: lem-sfb-prime-to-ell-linear-image-finite).

Proof plan:
1. If `M` has dimension zero, its automorphism group is trivial. Otherwise apply
   `lem-pod-profinite-stable-lattice` to obtain a stable free integer lattice spanning `M`,
   with its adic topology equal to the subspace topology. Choose an integer basis, also
   an `E`-basis, to write the action as integral invertible matrices.
2. Reduce modulo the `n`th power of the uniformizer, for `n ≥ 1`. These rings are finite
   by `lem-weil-valued-dvr-finite-quotients` and the coefficient datum. Evaluation on the
   finitely many basis vectors and openness of adic cosets prove continuity of reduction.
   Thus each reduction image `Q_n` is a finite continuous quotient of `H`, with order
   prime to `l`. Write `K_n` for its kernel.
3. Multiplication gives `(I + π^n B)^m = I + m π^n B` modulo `π^(n+1)` for `n ≥ 1`:
   induct on `m`, since `2*n ≥ n+1`. The coefficient datum gives `l ∈ π O`, so the
   `l`th power is the identity modulo `π^(n+1)`, also for `l = 2` and ramified extensions.
4. Inductively `K_1 = K_n`: if `h ∈ K_n`, its next reduction has `l`th power one.
   `lem-sfb-finite-matrix-group-coprime-power` makes that power map injective on `Q_(n+1)`,
   so `h ∈ K_(n+1)`. The reverse inclusion follows by reduction modulo `π`.
5. If `h ∈ K_1`, each entry of its matrix minus the identity lies in every `π^n O`.
   Its absolute value is bounded by `|π|^n`, which tends to zero, hence the entry is zero.
   Thus `ker ρ = K_1`, and reduction identifies `ρ.range` with `Q_1`. This proves
   finiteness and the asserted coprimality. -/
theorem primeToEll_linear_image_finite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [tE : TopologicalSpace E]
    (_hE : tE =
      (spectralNorm.nontriviallyNormedField ℚ_[l] E).toUniformSpace.toTopologicalSpace)
    (H : ProfiniteGrp.{v})
    (_hH : ∀ N : OpenNormalSubgroup H, Nat.Coprime (Nat.card (H ⧸ N.toSubgroup)) l)
    (M : Type w) [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    [TopologicalSpace M] [IsModuleTopology E M]
    (ρ : H →* (M ≃ₗ[E] M)) (_hρ : Continuous (fun p : H × M ↦ ρ p.1 p.2)) :
    Finite ρ.range ∧ Nat.Coprime (Nat.card ρ.range) l := by
  sorry

end Padic
