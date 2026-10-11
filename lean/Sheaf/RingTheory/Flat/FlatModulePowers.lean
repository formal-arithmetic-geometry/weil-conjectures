/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Flatness from flatness modulo every power of an ideal

Source: Stacks Project, Algebra, Lemma 10.99.11 (Tag 0523)
(blueprint: lem-weil-pbc-flat-module-powers).
-/

universe u v w

namespace Module.Flat

/-- Stacks Project, Algebra, Lemma 10.99.11 (Tag 0523)
(blueprint: lem-weil-pbc-flat-module-powers). The algebra structure represents the ring map
`R → S`, and the scalar tower says that the `R`-action on `M` is its restriction.

Proof:
1. Fix `q` containing `IS`, and put `p = q.comap (algebraMap R S)`. For the multiplication
   `μ : I ⊗[R] M → M`, its kernel `K` is an `S`-submodule. The image of
   `I^n ⊗[R] M → I ⊗[R] M` is `I^(n-1) (I ⊗[R] M)`, also equal to
   `(IS)^(n-1) (I ⊗[R] M)` by moving scalars across tensors.
2. Flatness of `M/I^n M` makes `I/I^n ⊗[R/I^n] M/I^n M → M/I^n M` injective.
   Tensoring over a quotient ring (`lem-weil-pbc-tensor-over-quotient-ring`) and right
   exactness (`lem-weil-pbc-tensor-right-exact`) identify its domain with
   `(I ⊗[R] M)/I^(n-1)(I ⊗[R] M)`. Thus `K` lies in every such power.
3. Noetherianity of `R` and finiteness of `M` make `I ⊗[R] M` finite over `S`.
   The Krull-intersection localization lemma (`lem-weil-pbc-krull-intersection-localization`,
   Stacks 00IQ) therefore gives `K_q = 0`.
4. Exactness of module localization (`lem-weil-pbc-localization-module-exact`) and its
   compatibility with tensor over the base (`lem-weil-pbc-localization-tensor-over-base`)
   imply that `M_q ⊗[R] I → M_q` is injective.
5. The induced map `R_p → S_q` is local; both rings are Noetherian
   (`lem-weil-pbc-localization-noetherian`), `J = I R_p` is proper, and `M_q` is finite over
   `S_q`.
6. Flatness of `R_p` over `R` (`lem-weil-pbc-localization-flat`) identifies `R_p ⊗[R] I`
   with `J`. Cancellation of base change (`lem-weil-pbc-module-tensor-cancel-base-change`)
   transfers the injectivity in step 4 to `M_q ⊗[R_p] J → M_q`.
7. Localizing the flat `R/I`-module `M/IM` preserves flatness and identifies its localization
   with `M_q/J M_q`. The quotient-localization identification
   (`lem-weil-pbc-localization-at-prime-of-quotient`) and flatness over localization
   (`lem-weil-pbc-flat-over-localization`) make this flat over `R_p/J`.
8. The variant local flatness criterion (`lem-weil-pbc-flat-variant-local-criterion`,
   Stacks 00ML) gives flatness over `R_p`; `lem-weil-pbc-flat-over-localization` then gives
   flatness over `R`.
9. If `S` is local and `IS` is in its maximal ideal, use that ideal for `q`. All its
   denominators are units, so `M → M_q` is an `R`-linear isomorphism and `M` is flat. -/
theorem flat_of_flat_quotients_powers {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M] (I : Ideal R)
    (hflat : ∀ n : ℕ, 1 ≤ n →
      Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n) • (⊤ : Submodule R M))) :
    (∀ (q : Ideal S) [q.IsPrime], I.map (algebraMap R S) ≤ q →
      Module.Flat R (LocalizedModule q.primeCompl M)) ∧
    (∀ [IsLocalRing S], I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S →
      Module.Flat R M) := sorry

end Module.Flat
