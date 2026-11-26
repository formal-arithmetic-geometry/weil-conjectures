/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.CompletionAtQuasiFinitePrimeMap
import WeilConjectures.RingTheory.CompletionAtQuasiFinitePrimeSplit
import WeilConjectures.RingTheory.QuasiFiniteAtFiniteSubalgebraAway

@[expose] public section

universe u v

/-!
# Completion at a quasi-finite prime is a direct factor

If `S` is of finite type over a Noetherian ring `R` and quasi-finite at a prime `q` over `p`,
then the completion of `S_q` is a direct factor of `R_p^∧ ⊗[R] S`, split off by the natural
projection.

## Implementation details

The local map is `Localization.localRingHom` and the completions are taken at the maximal
ideals of the localizations, as in `AdicCompletion.completion_finite_extension`. The map `ψ` is
characterized on every quotient coordinate, so it is the map induced on completions. The
formula for `φ` on pure tensors specifies the natural projection, including its compatibility
with both the `S`-action and the completed-base action.

The proof chooses a finite subalgebra `S'` and `g ∉ q` with `S'_g ≅ S_g`, applies the
decomposition of the completion of a finite extension to `R_p^∧ ⊗[R] S'`, and transports the
idempotent splitting along the inclusion after inverting `g`.

## References

* [Stacks, Tag 07NC]
-/

namespace Algebra

/-- If `S` is of finite type over a Noetherian ring `R` and quasi-finite at `q` over `p`, then
`R_p^∧ ⊗[R] S ≅ S_q^∧ × B` for some ring `B`, where the first component is the natural map
`φ` induced by the map of completions `ψ : R_p^∧ → S_q^∧`. -/
theorem completion_at_quasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [IsNoetherianRing R]
    (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    let U := TensorProduct R Rph S
    ∃ ψ : Rph →+* Sqh,
      (∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a)) ∧
      ∃ (B : Type (max u v)) (_ : CommRing B) (β : U →+* B) (φ : U →+* Sqh),
        (∀ (x : Rph) (y : S),
          φ (TensorProduct.tmul R x y) =
            ψ x * algebraMap Sq Sqh (algebraMap S Sq y)) ∧
        ∃ e : U ≃+* Sqh × B, e.toRingHom = RingHom.prod φ β := by
  dsimp
  obtain ⟨S', hfinite, g, hg, haway⟩ :=
    exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime R S q hq
  let : Module.Finite R S' := hfinite
  obtain ⟨ψ, hψ⟩ := exists_completion_map_atPrime R S q
  obtain ⟨B, _inst, β, φ, hφ, e, he⟩ :=
    completion_split_of_finite_subalgebra_away R S q S' g hg haway ψ hψ
  exact ⟨ψ, hψ, B, inferInstance, β, φ, hφ, e, he⟩

end Algebra
