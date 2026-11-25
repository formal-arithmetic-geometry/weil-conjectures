/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization of an idempotent section

An `R`-algebra section `s : S → R` with `s e = 1` and kernel `(1 - e)` for an idempotent `e`
identifies the localization `S[1/e]` with `R`.

## Implementation details

With the `S`-algebra structure on `R` through `s`, the map is surjective with kernel `(1 - e)`,
so `IsLocalization.away_of_isIdempotentElem` makes `R` a localization of `S` away from `e`.

## References

* [Stacks, Tag 00U8]
* [Stacks, Tag 00EH]
-/

@[expose] public section

universe u v

namespace Algebra.Etale

/-- Let `s : S → R` be an `R`-algebra section and `e` an idempotent with `s e = 1` and
`ker s = (1 - e)`. Then there is an `R`-algebra equivalence `S[1/e] ≃ R` extending `s`.
-/
theorem exists_localization_equiv_of_idempotent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (s : S →ₐ[R] R) (e : S) (he : IsIdempotentElem e) (hse : s e = 1)
    (hker : RingHom.ker s.toRingHom = Ideal.span {1 - e}) :
    ∃ ψ : Localization.Away e ≃ₐ[R] R,
      ∀ x : S, ψ (algebraMap S (Localization.Away e) x) = s x := by
  let : Algebra S R := s.toRingHom.toAlgebra
  have hs : Function.Surjective (algebraMap S R) :=
    fun r ↦ ⟨e * algebraMap R S r, by
      change s (e * algebraMap R S r) = r
      simp [hse]⟩
  let : IsLocalization.Away e R := IsLocalization.away_of_isIdempotentElem he hker hs
  let φ := IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e) R
  have hφ (x : S) : φ (algebraMap S (Localization.Away e) x) = s x :=
    φ.commutes x
  let ψ : Localization.Away e ≃ₐ[R] R := AlgEquiv.ofRingEquiv (f := φ.toRingEquiv)
    (fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S (Localization.Away e)]
      exact (hφ (algebraMap R S r)).trans (s.commutes r))
  exact ⟨ψ, hφ⟩

end Algebra.Etale
