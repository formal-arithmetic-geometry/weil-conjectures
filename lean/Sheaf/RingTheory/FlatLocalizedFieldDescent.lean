/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Descent from a field localization along a flat ring map

Source: Stacks Project, Algebra, Tags 00HT (lemma-flat-localization),
00HR (lemma-local-flat-ff), and 05CK (lemma-faithfully-flat-universally-injective);
Curves, Tag 0C4D (lemma-nodal), arbitrary-field descent paragraph
(blueprint: lem-trf-flat-localized-field-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- Localizing a flat ring map at a prime above a maximal ideal gives a flat local,
faithfully flat, injective map. If the target localization is a field, the extended
maximal ideal vanishes and the canonical residue map is an isomorphism of base algebras.
The residue map is the quotient by the localized maximal ideal followed by the inverse
of Mathlib's canonical residue-field identification; on fractions it sends `r/s` to
`r̄/s̄` by `IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk`.

Source: Stacks Project, Algebra, Tags 00HT, 00HR, 05CK; Curves, Tag 0C4D,
lemma-nodal, arbitrary-field descent paragraph
(blueprint: lem-trf-flat-localized-field-descent).

Proof:
1. The equality of contracted primes sends denominators outside `p` outside `q`.
   The canonical `Localization.localRingHom` is therefore well defined and flat and
   local by lem-weil-pbc-flat-local-ring-maps and def-weil-pbc-localization-at-prime.
2. Apply lem-weil-pbc-flat-local-hom-faithfully-flat to obtain faithful flatness.
   Contract the zero ideal by lem-weil-pbc-faithfully-flat-ideal-contraction to obtain
   injectivity.
3. If the target is a field, its proper maximal ideal is zero. Locality sends the
   extended ideal `p` into zero; injectivity makes the extended ideal itself zero.
4. Maximality of `p` makes every denominator invertible modulo `p`. The fraction map
   `r/s ↦ r̄/s̄` is well defined: reduce the localization fraction relation modulo `p`
   and cancel its denominator. The fraction formulas show it is a ring map and sends
   `r/1` to `r̄`, hence respects the base algebra structure. It is surjective by these
   elements. A fraction in its kernel has numerator in `p`, so vanishes by step 3.
   Its inverse thus gives the asserted algebra equivalence, with underlying ring map
   the canonical composite displayed in the conclusion. -/
theorem flat_localized_field_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat)
    (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap φ) :
    (Localization.localRingHom p q φ hpq).Flat ∧
      IsLocalHom (Localization.localRingHom p q φ hpq) ∧
      (Localization.localRingHom p q φ hpq).FaithfullyFlat ∧
      Function.Injective (Localization.localRingHom p q φ hpq) ∧
      (IsField (Localization.AtPrime q) →
        p.map (algebraMap R (Localization.AtPrime p)) = ⊥ ∧
          ∃ e : Localization.AtPrime p ≃ₐ[R] R ⧸ p,
            e.toRingHom =
              (IsLocalization.AtPrime.equivQuotMaximalIdeal p
                (Localization.AtPrime p)).symm.toRingHom.comp
                  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime p)))) := by
  sorry

end RingHom
