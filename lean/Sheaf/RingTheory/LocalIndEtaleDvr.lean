/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.FieldTheory.Separable

import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.RingTheory.ProEtale.IndEtale
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Local ind-etale extensions of discrete valuation rings

Source: Stacks Project, More on Algebra, Tags 0AP2, 0AH1 and 092R;
Algebra, Tags 00PD, 00DK and 00E3, with the local filtered-colimit refinement
(blueprint: lem-sfb-local-ind-etale-dvr).

## Main statements

* `IsDiscreteValuationRing.local_indEtale`: the local extension is a DVR with the same
  uniformizer and separable algebraic fraction field, without assuming it Noetherian.
* `IsDiscreteValuationRing.local_indEtale_tensor_atPrime`: the corresponding assertion
  after arbitrary algebra base change and localization at a prime over a DVR point.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- A nonzero local ind-etale algebra over a DVR is a DVR with unchanged uniformizer
and separable algebraic fraction-field extension. The fraction-field algebra is the
canonical extension of the injective structural map, not an arbitrary field embedding.

Source: Stacks Project, Tags 0AP2, 0AH1, 00PD and 092R, local colimit refinement
(blueprint: lem-sfb-local-ind-etale-dvr).

Proof:
1. Present the algebra as a filtered colimit of etale algebras. Localize each at the
   contracted maximal ideal, using lem-weil-pbc-filtered-colimit-localization-at-prime.
   By lem-sbc-etale-trait-stalk and lem-weil-pbc-affine-open-stalk-localization each
   localized stage is a DVR with the given uniformizer and injective structural map.
2. By lem-weil-pbc-dvr-unit-times-uniformizer-power each nonzero stage element is a
   unit times a power of the uniformizer. Transition maps preserve this expression
   and are injective. The elementwise criterion of
   lem-pc-filtered-colimit-commrings-elementwise makes the colimit legs injective;
   common-stage representatives show that the colimit is a domain.
3. Every nonzero colimit element has the same unit-times-power form. Its exponent
   is unique by cancellation and the nonunit property of the uniformizer. In a
   nonzero ideal choose an element of least exponent: its power generates the ideal.
   Thus every ideal is principal. The maximal ideal consists of the positive powers,
   by lem-weil-pbc-local-ring-unit-criterion. This gives a local PID that is not a field.
4. Apply lem-trf-ind-etale-residue-separable at the prime pulled back from zero in
   the localized domain. Its residue field is the fraction field of the colimit,
   compatibly with the base fraction field, by
   lem-weil-pbc-localization-prime-residue-field-iso.
5. The original local algebra is its own localization at its maximal ideal: all
   denominators are units by lem-weil-pbc-local-ring-unit-criterion. Transport the
   conclusions back along this canonical identification. No Noetherian hypothesis
   on the target is used. For different universes first use the canonical ULifts
   in RingHom.IndEtaleAcrossUniverses and transport back along their ring equivalences. -/
theorem local_indEtale
    (U : Type u) (T : Type v) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [CommRing T] [IsLocalRing T] [Algebra U T]
    (π : U) (hπ : IsLocalRing.maximalIdeal U = Ideal.span {π})
    (hind : RingHom.IndEtaleAcrossUniverses (algebraMap U T))
    (hlocal : Ideal.comap (algebraMap U T) (IsLocalRing.maximalIdeal T) =
      IsLocalRing.maximalIdeal U) :
    ∃ (_ : IsDomain T) (_ : IsDiscreteValuationRing T)
      (hinj : Function.Injective (algebraMap U T)),
      IsLocalRing.maximalIdeal T = Ideal.span {algebraMap U T π} ∧
      @Algebra.IsSeparable (FractionRing U) (FractionRing T) _ _
        (IsFractionRing.map (K := FractionRing U) (L := FractionRing T) hinj).toAlgebra := by
  sorry

/-- Localizing an arbitrary base change of a local ind-etale DVR extension at a prime
above a DVR point preserves the DVR and all its uniformizers.

Source: Stacks Project, Tags 00DK, 00E3 and the local argument of Tags 0AP2 and 00PD
(blueprint: lem-sfb-local-ind-etale-dvr).

Proof: Put A = T tensor_U D and R = D_p. By lem-weil-pbc-ind-etale-stability,
E = T tensor_U R is ind-etale over R. By lem-weil-pbc-localization-tensor-over-base,
after switching factors, A to E localizes at the images of D outside p; on fractions
it sends t tensor (d/s) to (t tensor d)/(1 tensor s). This identification respects
multiplication and one. These denominators avoid q since its contraction is p.
By lem-weil-pbc-localization-prime-residue-field-iso, q extends to a prime r of E,
A_q is canonically E_r over D, and r contracts to pR. Apply the localized-stage,
injective-colimit and least-exponent arguments in local_indEtale to R, E and r.
They give a domain DVR, injectivity of the canonical local map, and preservation of
any uniformizer of R. Its maximal ideal is pR, so the extended ideals pA_q and qA_q
are equal. Canonical ULift transport handles different ring universes as above. -/
theorem local_indEtale_tensor_atPrime
    (U : Type u) (T : Type v) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [CommRing T] [IsLocalRing T] [Algebra U T]
    (hind : RingHom.IndEtaleAcrossUniverses (algebraMap U T))
    (hlocal : Ideal.comap (algebraMap U T) (IsLocalRing.maximalIdeal T) =
      IsLocalRing.maximalIdeal U)
    (D : Type w) [CommRing D] [Algebra U D]
    (p : Ideal D) [p.IsPrime] (q : Ideal (T ⊗[U] D)) [q.IsPrime]
    (hpq : p = q.comap (Algebra.TensorProduct.includeRight : D →ₐ[U] T ⊗[U] D).toRingHom)
    [IsDomain (Localization.AtPrime p)] [IsDiscreteValuationRing (Localization.AtPrime p)] :
    ∃ (_ : IsDomain (Localization.AtPrime q))
      (_ : IsDiscreteValuationRing (Localization.AtPrime q)),
      Function.Injective (Localization.localRingHom p q
        (Algebra.TensorProduct.includeRight : D →ₐ[U] T ⊗[U] D).toRingHom hpq) ∧
      (∀ (t : Localization.AtPrime p),
        IsLocalRing.maximalIdeal (Localization.AtPrime p) = Ideal.span {t} →
        IsLocalRing.maximalIdeal (Localization.AtPrime q) =
          Ideal.span {Localization.localRingHom p q
            (Algebra.TensorProduct.includeRight : D →ₐ[U] T ⊗[U] D).toRingHom hpq t}) ∧
      p.map ((algebraMap (T ⊗[U] D) (Localization.AtPrime q)).comp
        (Algebra.TensorProduct.includeRight : D →ₐ[U] T ⊗[U] D).toRingHom) =
        q.map (algebraMap (T ⊗[U] D) (Localization.AtPrime q)) := by
  sorry

end IsDiscreteValuationRing
