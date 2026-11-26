/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.NoetherNormalizationOverDomainSurjective

/-!
# Noether normalization over a domain

An injective finite type algebra over a domain contains a finite extension of a polynomial
subalgebra which becomes the whole algebra after inverting a nonzero base element.

## Implementation details

Apply Noether normalization over the fraction field, rescale the variables so that the
coordinates lie in `S`, clear the denominators of the integral equations of the generators by a
common nonzero `f`, and replace each generator `xᵢ` by `f * xᵢ`.

## References

* [Stacks, Tag 07NA]
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra.FiniteType

/-- An injective finite type algebra `S` over a domain `R` contains a finite extension of a
polynomial subalgebra which becomes the whole algebra after inverting a nonzero element of `R`. -/
theorem exists_finite_subalgebra_away
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (d : ℕ) (y : Fin d → S) (S' : Subalgebra R S),
      Function.Injective (MvPolynomial.aeval (R := R) y) ∧
      ∃ h : (MvPolynomial.aeval (R := R) y).range ≤ S',
        (letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
         Module.Finite (MvPolynomial.aeval (R := R) y).range S') ∧
        ∃ f : R, f ≠ 0 ∧
          Function.Bijective
            (IsLocalization.Away.map
              (Localization.Away (algebraMap R S' f))
              (Localization.Away (S'.val (algebraMap R S' f)))
              S'.val.toRingHom (algebraMap R S' f)) := by
  obtain ⟨d, y, S', hay, h, hfin, f, hf, hsurj⟩ :=
    exists_finite_subalgebra_away_surjective R S hinj
  refine ⟨d, y, S', hay, h, hfin, f, hf, ?_⟩
  refine ⟨IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, hsurj⟩

end Algebra.FiniteType
