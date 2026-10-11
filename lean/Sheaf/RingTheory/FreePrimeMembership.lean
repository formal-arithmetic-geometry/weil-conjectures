/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Prime membership in a finite free module after localization

Source: Stacks Project, Algebra, Definition Tag 00CO and the localization at a prime;
the coordinate calculation underlying Lemma Tag 00NX
(blueprint: lem-sc-free-prime-membership).
-/

universe u

namespace Module

/-- Prime membership in `R^n` is detected after localization at the same prime, and each
coordinate satisfies the corresponding scalar criterion.

Source: Stacks Project, Algebra, Definition Tag 00CO, module localization Tag 07JZ,
and the finite-free coordinate calculation underlying Lemma Tag 00NX
(blueprint: lem-sc-free-prime-membership).

Here `F = Fin n → R`, `S = p.primeCompl`, `F_p = LocalizedModule S F`
[def-weil-pbc-module-localization], and `R_p = Localization.AtPrime p`
[def-weil-pbc-localization-at-prime]. The extended ideal `p.map (algebraMap R R_p)`
acting on the top submodule is `pF_p`; `p • ⊤` is `pF`.

Proof (the node's single step): identify the localization of the finite product `R^n`
with the finite product of `R_p` using coordinate projections and common denominators
[def-weil-pbc-module-localization]. Membership in `pF_p` is coordinatewise membership
in the extended ideal `pR_p`. For a coordinate `a`, the scalar localization criterion
[def-weil-pbc-localization-at-prime] says that `a/1 ∈ pR_p` exactly when `ua ∈ p`
for some `u ∉ p`. Primality implies `a ∈ p`; conversely, use the denominator `1`.
Thus all localized coordinates lie in `pR_p` exactly when all original coordinates
lie in `p`, which is precisely membership in `pR^n`.
-/
theorem free_prime_mem_localized_iff
    {R : Type u} [CommRing R] (n : ℕ) (s : Fin n → R) (p : Ideal R) [p.IsPrime] :
    (LocalizedModule.mkLinearMap p.primeCompl (Fin n → R) s ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p)
            (LocalizedModule p.primeCompl (Fin n → R))) ↔
      s ∈ p • (⊤ : Submodule R (Fin n → R))) ∧
    (∀ i : Fin n,
      algebraMap R (Localization.AtPrime p) (s i) ∈
          Ideal.map (algebraMap R (Localization.AtPrime p)) p ↔ s i ∈ p) := by
  sorry

end Module
