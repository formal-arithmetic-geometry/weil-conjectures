/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Compatible normalized unit-root lifts of local DVR diagrams

Source: Stacks Project, Tag 0BRM, first claim in the proof of `lemma-abhyankar`;
Tag 0BQL identifies the selected finite étale components with integral closures.
(blueprint: lem-sfb-dvr-unit-root-normalized-lift)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace RingTheory

/-- Adjoining a root of a unit gives compatible normalization branches over a local
inclusion of DVRs. The two named subalgebras are the actual integral closures.
The maps out of them and their localizations are specified on the canonical generators;
thus they are the canonical maps, rather than arbitrary maps of the same rings.

Source: Stacks Project, Tag 0BRM, first claim of `lemma-abhyankar`, with Tag 0BQL.
(blueprint: lem-sfb-dvr-unit-root-normalized-lift)

Proof:
1. A DVR is a PID, hence Noetherian and integrally closed
   (lem-weil-pbc-pid-noetherian-normal). Its spectrum is normal integral Noetherian:
   identify its stalks with prime localizations and its generic stalk with its fraction
   field (lem-weil-pbc-spec-domain-stalks-function-field), and use preservation of
   normality under localization (lem-weil-pbc-localization-normal-domain).
2. Form C = S[X]/(X^h-u) and B = T[X]/(X^h-u). The root is a unit and h is a unit,
   so the derivative is a unit. The standard étale derivative criterion makes these
   algebras étale (lem-weil-pbc-standard-etale-monic-derivative), and their integral
   root generators make them finite (lem-weil-pbc-finite-of-integral-generators).
   Monic division shows both algebras are nonzero, including when h = 1.
3. Choose a nonempty component of Spec B. The normal generic component theorem
   (lem-sfb-finite-etale-normal-generic-components) identifies it with the integral
   closure E in a finite separable field F' = F(r). Inside F' take N' = N[r]. This
   finite dimensional domain is a field: multiplication by a nonzero element is
   injective and therefore surjective. The surjection N[X]/(X^h-u) -> N' selects
   one factor of its finite product of separable generic fields. The same component
   theorem therefore identifies its normalization D as finite étale over S.
4. The inclusion N' -> F' restricts to D -> E, since monic equations over S remain
   monic over T. Choose a prime b above the closed point of T, using surjectivity of
   the selected finite étale component, and contract to a in D. Locality of S -> T
   gives the required contraction to the closed point of S. Both primes are maximal
   by integrality (lem-weil-pbc-integral-prime-over-maximal-maximal).
5. Localize at a and b. The fraction map d/s -> d/s is defined because the prime
   contraction identifies the allowed denominators. These maps are injective, local,
   and commute. The root is integral by its monic equation, hence belongs to D and
   its localization. The localization embedding into N' is fixed on D by inclusion.
6. Apply lem-sbc-etale-trait-stalk to Spec D -> Spec S and Spec E -> Spec T at a,b.
   The affine stalk identification gives the actual localizations and maps. The
   stalks are DVRs with the same uniformizers, giving both maximal-ideal identities.
7. Apply lem-weil-pbc-etale-algebra-residue-field-separable to the two finite étale
   components at a,b. Identifying prime residue fields with the quotients of their
   localizations gives finite separable residue extensions via the canonical maps.
No assumption of algebraicity, finiteness or residue separability on F/N is used. -/
theorem exists_dvr_unit_root_normalized_lift
    (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (T : Type v) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra S T] (hinj : Function.Injective (algebraMap S T))
    [IsLocalHom (algebraMap S T)]
    (N : Type w) [Field N] [Algebra S N] [IsFractionRing S N]
    (F : Type z) [Field F] [Algebra T F] [IsFractionRing T F]
    [Algebra N F] [Algebra S F] [IsScalarTower S T F] [IsScalarTower S N F]
    (h : ℕ) (hh : 1 ≤ h) (hunit : IsUnit (h : S)) (u : Sˣ) :
    ∃ (N' : Type w) (_ : Field N') (_ : Algebra N N')
      (_ : Algebra S N') (_ : IsScalarTower S N N')
      (F' : Type z) (_ : Field F') (_ : Algebra F F')
      (_ : Algebra T F') (_ : IsScalarTower T F F')
      (i : N' →+* F') (r : N'),
      FiniteDimensional N N' ∧ Algebra.IsSeparable N N' ∧
      FiniteDimensional F F' ∧ Algebra.IsSeparable F F' ∧
      i.comp (algebraMap N N') = (algebraMap F F').comp (algebraMap N F) ∧
      r ^ h = algebraMap S N' (u : S) ∧
      IntermediateField.adjoin N ({r} : Set N') = ⊤ ∧
      IntermediateField.adjoin F ({i r} : Set F') = ⊤ ∧
      ∃ (D : Subalgebra S N') (E : Subalgebra T F') (d : D →+* E),
        D = integralClosure S N' ∧ E = integralClosure T F' ∧
        (∀ x : D, (d x : F') = i (x : N')) ∧
        ∃ (a : Ideal D) (_ : a.IsMaximal) (b : Ideal E) (_ : b.IsMaximal)
          (hab : a = b.comap d),
          a.comap (algebraMap S D) = IsLocalRing.maximalIdeal S ∧
          b.comap (algebraMap T E) = IsLocalRing.maximalIdeal T ∧
          ∃ (_ : IsDiscreteValuationRing (Localization.AtPrime a))
            (_ : IsDiscreteValuationRing (Localization.AtPrime b))
            (_ : Algebra S (Localization.AtPrime a))
            (_ : Algebra T (Localization.AtPrime b))
            (_ : IsLocalHom (algebraMap S (Localization.AtPrime a)))
            (_ : IsLocalHom (algebraMap T (Localization.AtPrime b)))
            (j : Localization.AtPrime a →+* N'),
            algebraMap S (Localization.AtPrime a) =
              (algebraMap D (Localization.AtPrime a)).comp (algebraMap S D) ∧
            algebraMap T (Localization.AtPrime b) =
              (algebraMap E (Localization.AtPrime b)).comp (algebraMap T E) ∧
            (∀ x : D, j (algebraMap D (Localization.AtPrime a) x) = (x : N')) ∧
            (∃ r₁ : Localization.AtPrime a, j r₁ = r) ∧
            Function.Injective (algebraMap S (Localization.AtPrime a)) ∧
            Function.Injective (algebraMap T (Localization.AtPrime b)) ∧
            Function.Injective (Localization.localRingHom a b d hab) ∧
            IsLocalHom (Localization.localRingHom a b d hab) ∧
            (Localization.localRingHom a b d hab).comp
                (algebraMap S (Localization.AtPrime a)) =
              (algebraMap T (Localization.AtPrime b)).comp (algebraMap S T) ∧
            (IsLocalRing.maximalIdeal S).map (algebraMap S (Localization.AtPrime a)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime a) ∧
            (IsLocalRing.maximalIdeal T).map (algebraMap T (Localization.AtPrime b)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime b) ∧
            FiniteDimensional (IsLocalRing.ResidueField S)
              (IsLocalRing.ResidueField (Localization.AtPrime a)) ∧
            Algebra.IsSeparable (IsLocalRing.ResidueField S)
              (IsLocalRing.ResidueField (Localization.AtPrime a)) ∧
            FiniteDimensional (IsLocalRing.ResidueField T)
              (IsLocalRing.ResidueField (Localization.AtPrime b)) ∧
            Algebra.IsSeparable (IsLocalRing.ResidueField T)
              (IsLocalRing.ResidueField (Localization.AtPrime b)) := by
  sorry

end RingTheory
