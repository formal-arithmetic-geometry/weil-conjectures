/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Module.TransferInstance

/-!
# Associated primes under flat base change

Source: Stacks Project, Algebra, Lemma Tag 0312 (Bourbaki)
(blueprint: lem-weil-pbc-associated-primes-flat-base-change).
-/

universe r s m n

open scoped TensorProduct Pointwise

namespace RingTheory

/-- Bourbaki's associated-prime formula for a flat module.
Source: Stacks Project, Algebra, Lemma Tag 0312
(blueprint: lem-weil-pbc-associated-primes-flat-base-change).
The `S`-action on `M ⊗[R] N` is transported along tensor commutation from the action on
`N ⊗[R] M`: thus `s • (m ⊗ n) = m ⊗ (s • n)`. The submodule `pN` is the
pointwise set scalar product `(p : Set R) • ⊤` in `Submodule S N`.

Proof, following the node's nine steps:
1. For `p = Ann(z)`, inject `R/p` into `M` by `r ↦ r z`. Flatness
   (def-weil-pbc-flat-ring-map, lem-weil-pbc-flat-tensor-exact) preserves this injection.
   Identify `(R/p) ⊗ N` with `N/pN` (lem-weil-pbc-tensor-over-quotient-ring).
   An injection preserves associated primes (lem-weil-pbc-associated-primes-exact-sequence).
2. Associated primes of a directed union of submodules are the union of their associated
   primes: each witnessing element already lies in one submodule, with the same annihilator.
3. Write `M` as the directed union of its finite submodules (def-weil-finitely-generated-module).
   Flatness embeds their tensors into `M ⊗ N`, with union the whole tensor. Step 2 reduces
   equality over Noetherian `R` (def-weil-pbc-noetherian-ring) to finite `M`.
4. For `q` associated to `M ⊗ N`, localize at `q` to obtain a nonzero element annihilated by
   `q S_q` (lem-weil-pbc-associated-prime-localize-at-prime). Set `p` to its contraction.
5. Identify `(M ⊗ N)_q` with `M_p ⊗ N_q`, compatibly with `R`-scalars, using
   lem-weil-pbc-localization-tensor-over-base and
   lem-weil-pbc-localization-module-over-localization (and the module-localization definition).
6. `N_q` remains flat over `R`: localize the injections induced by tensoring with `N`, using
   lem-weil-pbc-localization-module-exact and the naturality of the tensor identification.
7. If `p R_p` were not associated to `M_p`, choose a nonzerodivisor in it using
   lem-weil-pbc-nonzerodivisor-if-maximal-not-associated. Noetherian localization uses
   lem-weil-pbc-localization-noetherian. Flatness makes its action injective on `M_p ⊗ N_q`,
   contradicting Step 4. Descend association by
   lem-weil-pbc-noetherian-associated-prime-from-localization. Thus `p` is associated to `M`.
8. Choose a prime filtration of finite `M` (lem-weil-pbc-noetherian-module-prime-filtration).
   Tensor it with `N`, using flat tensor exactness and lem-weil-pbc-tensor-right-exact.
   Its quotients are `N/p_iN`. The exact-sequence associated-prime inclusion puts each
   associated `q` in the associated primes of one such quotient.
9. Step 7 applied to `R/p_i` shows that the contraction of this `q` is associated to `R/p_i`.
   Primality gives `Ass(R/p_i) = {p_i}`. Hence that `p_i` is the contraction `p` already
   associated to `M`, proving the reverse inclusion. All maps are `S`-linear. -/
theorem annihilatorAssociatedPrimes_flat_base_change
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type m) [AddCommGroup M] [Module R M]
    (N : Type n) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Flat R N] :
    letI : Module S (M ⊗[R] N) := (TensorProduct.comm R M N).toAddEquiv.module S
    let rhs : Set (Ideal S) := ⋃ p ∈ annihilatorAssociatedPrimes R M,
      annihilatorAssociatedPrimes S (N ⧸ ((p : Set R) • (⊤ : Submodule S N)))
    rhs ⊆ annihilatorAssociatedPrimes S (M ⊗[R] N) ∧
      (IsNoetherianRing R → annihilatorAssociatedPrimes S (M ⊗[R] N) = rhs) := by
  sorry

end RingTheory
