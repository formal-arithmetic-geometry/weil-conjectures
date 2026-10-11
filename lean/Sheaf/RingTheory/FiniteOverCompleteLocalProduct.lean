/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs

/-! # Finite algebras over complete local rings

Source: literature/stacks-project/algebra.tex, Lemma Tag 0325
(blueprint: lem-weil-pbc-finite-over-complete-local-product)
-/

universe u v

namespace Algebra

/-- A finite algebra over a complete Noetherian local ring is a finite product of
complete Noetherian local rings, with the domain case as stated in Tag 0325.

Proof (the six steps of the node):
1. By `lem-weil-pbc-finite-algebra-noetherian` (00FN), the finite algebra `S` over
   the Noetherian ring `R` is Noetherian.
2. By `lem-weil-pbc-completion-finite-extension` (05DR/07N9), there are finitely
   many primes of `S` over the maximal ideal `m` of `R`. By
   `lem-weil-pbc-finite-algebra-is-integral` and
   `lem-weil-pbc-integral-prime-over-maximal-maximal` (00GS(2)), they are maximal.
   Conversely, `lem-weil-pbc-finite-algebra-local-radical` says every maximal
   ideal lies over `m`; hence these are exactly the maximal ideals of `S`.
3. By `lem-weil-pbc-finite-module-complete-over-complete-noetherian` (00MA), `S`
   is complete as an `R`-module for `m`. The submodules `m^n S` are the ideals
   `(mS)^n`, so its canonical map to its `mS`-adic completion
   (`def-weil-pbc-adic-completion`) is a ring isomorphism.
4. Apply `lem-weil-pbc-completion-finite-extension` (07N9) at `m`. Since elements
   outside `m` are units, `R → R_m` is an isomorphism, and so is
   `S → S ⊗[R] R_m` (`def-weil-pbc-localization-at-prime`). Composing the induced
   completion isomorphism with step 3 gives `S ≃ ∏ q, (S_q)^`, over the finitely
   many maximal ideals, an isomorphism of `R`-algebras. Index the factors by
   `Fin t`. With no factors (`t = 0`) this is the zero ring.
5. Each `S_q` is local (`def-weil-pbc-localization-at-prime`) and Noetherian
   (`lem-weil-pbc-localization-noetherian`). Its completion is Noetherian by
   `lem-weil-pbc-adic-completion-noetherian` (05GH), and local by
   `lem-weil-pbc-local-completion-local-ring` (05GG), with maximal ideal extended
   from `q S_q`. By `lem-weil-pbc-module-completion-complete` (031C), it is
   complete for that ideal: its powers agree with the module filtration, as in
   step 3 (`def-weil-pbc-adically-complete-ring`).
6. If `S` is a domain, `e(1-e)=0` forces every idempotent to be zero or one.
   The empty product is impossible, and two nonzero local factors would give
   a nontrivial idempotent. There is therefore exactly one factor. Transport
   its local structure and completeness along the ring isomorphism. By step 2
   its maximal ideal lies over `m` and every prime over `m` is that maximal
   ideal; the quotient isomorphisms
   for all powers of the maximal ideal transport the canonical completion map
   (`def-weil-pbc-adically-complete-ring`).

Source: literature/stacks-project/algebra.tex, Lemma Tag 0325
(blueprint: lem-weil-pbc-finite-over-complete-local-product)
-/
theorem finite_over_complete_local_product
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Algebra R S] [Module.Finite R S] :
    IsNoetherianRing S ∧
      Finite {M : Ideal S // M.IsMaximal} ∧
      (∃ (t : ℕ) (A : Fin t → Type v) (rings : ∀ i, CommRing (A i)),
        letI := rings
        ∃ (algebras : ∀ i, Algebra R (A i)),
          letI := algebras
          ∃ (locals : ∀ i, IsLocalRing (A i)),
            letI := locals
            Nonempty (S ≃ₐ[R] (∀ i, A i)) ∧
              (∀ i, IsNoetherianRing (A i)) ∧
              (∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))) ∧
      (IsDomain S →
        IsNoetherianRing S ∧
          ∃ hL : IsLocalRing S,
            letI := hL
            IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
              (IsLocalRing.maximalIdeal S).comap (algebraMap R S) =
                IsLocalRing.maximalIdeal R ∧
              ∀ M : Ideal S, M.IsPrime →
                M.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
                  M = IsLocalRing.maximalIdeal S) := by
  sorry

end Algebra
