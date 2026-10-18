/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.GroupTheory.FineMonoidFiniteSaturation
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Normalization of an affine torsion-free monoid algebra

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, Lemma 3.2.9 and its proof, printed
p. 104, and saturation in 3.1.17 (blueprint: lem-trf-affine-monoid-algebra-normalization).

The multiplicative notation of `MonoidAlgebra` and `FineFan.IsFine` presents exactly the
additive monoids in the source: `1` means `0` and `g ^ n` means `n • g`.
-/

set_option autoImplicit false

universe u v

open Algebra AlgebraicGeometry

namespace MonoidAlgebra

/-- The canonical monoid map to its saturation in its group completion: first take its
range in the completion, then the recorded inclusion into saturation.
Source: ILO VIII 3.1.17 (blueprint: lem-trf-affine-monoid-algebra-normalization). -/
def normalizationMonoidMap (P : Type u) [CommMonoid P] :
    P →* FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P))) :=
  (FineFan.intoSaturation (MonoidHom.mrange (GrothendieckGroup.of (M := P)))).comp
    (GrothendieckGroup.of (M := P)).mrangeRestrict

/-- The canonical monomial map from the monoid algebra to its saturated monoid algebra.
Source: ILO VIII 3.2.9 (blueprint: lem-trf-affine-monoid-algebra-normalization). -/
noncomputable def normalizationAlgebraMap (k : Type v) [Field k]
    (P : Type u) [CommMonoid P] :
    MonoidAlgebra k P →+*
      MonoidAlgebra k
        (FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P)))) :=
  mapDomainRingHom k (normalizationMonoidMap P)

/-- The saturated monoid algebra maps into the group algebra by its subtype inclusion.
Source: ILO VIII 3.2.9 (blueprint: lem-trf-affine-monoid-algebra-normalization). -/
noncomputable def normalizationAmbientMap (k : Type v) [Field k]
    (P : Type u) [CommMonoid P] :
    MonoidAlgebra k
      (FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P)))) →+*
      MonoidAlgebra k (GrothendieckGroup P) :=
  mapDomainRingHom k (FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P)))).subtype

/-- The canonical map from the original monoid algebra into the total fraction ring
of its group algebra. Under the theorem's hypotheses this total fraction ring is a field.
Source: ILO VIII 3.2.9 (blueprint: lem-trf-affine-monoid-algebra-normalization). -/
noncomputable def normalizationFractionMap (k : Type v) [Field k]
    (P : Type u) [CommMonoid P] :
    MonoidAlgebra k P →+* FractionRing (MonoidAlgebra k (GrothendieckGroup P)) :=
  (algebraMap (MonoidAlgebra k (GrothendieckGroup P))
    (FractionRing (MonoidAlgebra k (GrothendieckGroup P)))).comp
      (mapDomainRingHom k (GrothendieckGroup.of (M := P)))

/-- The canonical map from the saturated monoid algebra into that same fraction ring.
Source: ILO VIII 3.2.9 (blueprint: lem-trf-affine-monoid-algebra-normalization). -/
noncomputable def normalizationSaturatedFractionMap (k : Type v) [Field k]
    (P : Type u) [CommMonoid P] :
    MonoidAlgebra k
      (FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P)))) →+*
      FractionRing (MonoidAlgebra k (GrothendieckGroup P)) :=
  (algebraMap (MonoidAlgebra k (GrothendieckGroup P))
    (FractionRing (MonoidAlgebra k (GrothendieckGroup P)))).comp
      (normalizationAmbientMap k P)

/-- A fine monoid with torsion-free group completion has finite saturated monoid algebra,
which is exactly its integral closure in the common fraction field. No sharpness or positive
rank is required.

Source: ILO VIII, Lemma 3.2.9 and proof, p. 104, and 3.1.17, p. 101
(blueprint: lem-trf-affine-monoid-algebra-normalization).

Proof:
1. Apply `fine_monoid_finite_saturation` (lem-trf-fine-monoid-finite-saturation): saturation
   is finitely generated, has the same completion, and gives a finite monoid-algebra map.
2. Apply lem-trf-monoid-algebra-domain-fraction to the monoid and its saturation. Their
   monomial maps are injective, all three algebras are domains, and their fraction fields agree.
3. By lem-trf-monomial-integrality every saturated monomial, and hence every finite sum of
   them, is integral over the original algebra. This gives one inclusion in the integral closure.
4. By lem-trf-fg-torsionfree-group-free, the completion has a finite integral basis. Iterating
   lem-weil-pbc-polynomial-ring-normal-domain gives a normal polynomial ring, including the
   coefficient field when the rank is zero.
5. Identify the group algebra with the localization of this polynomial ring at the variables:
   send variables to basis monomials; the inverse sends an exponent vector to the quotient of
   its positive and negative monomials. The two composites fix coefficients and monomials.
6. By lem-weil-pbc-localization-normal-domain the group algebra is normal in its fraction
   field. An element integral over the original algebra is therefore in the group algebra.
7. Apply lem-trf-integral-support-saturation to its finite support: every exponent belongs
   to the saturation, so the element is in the saturated algebra. This proves the equivalence.
8. For an element of the fraction field integral over the saturated algebra, ambient normality
   first puts it in the group algebra. Apply lem-trf-saturated-monoid-algebra-normal to put it
   in the saturated algebra. This proves integral closedness in the entire fraction field.
All steps allow units and rank zero. -/
theorem affine_monoid_algebra_normalization (k : Type v) [Field k]
    (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P)
    [IsMulTorsionFree (GrothendieckGroup P)] :
    Function.Injective (normalizationAlgebraMap k P) ∧
    Function.Injective (normalizationAmbientMap k P) ∧
    Function.Injective
      (algebraMap (MonoidAlgebra k (GrothendieckGroup P))
        (FractionRing (MonoidAlgebra k (GrothendieckGroup P)))) ∧
    IsDomain (MonoidAlgebra k P) ∧
    IsDomain (MonoidAlgebra k
      (FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P))))) ∧
    IsDomain (MonoidAlgebra k (GrothendieckGroup P)) ∧
    @IsFractionRing (MonoidAlgebra k P) _
      (FractionRing (MonoidAlgebra k (GrothendieckGroup P))) _
      (normalizationFractionMap k P).toAlgebra ∧
    @IsFractionRing
      (MonoidAlgebra k
        (FineFan.saturation (MonoidHom.mrange (GrothendieckGroup.of (M := P))))) _
      (FractionRing (MonoidAlgebra k (GrothendieckGroup P))) _
      (normalizationSaturatedFractionMap k P).toAlgebra ∧
    (∀ x : FractionRing (MonoidAlgebra k (GrothendieckGroup P)),
      (normalizationFractionMap k P).IsIntegralElem x ↔
        x ∈ Set.range (normalizationSaturatedFractionMap k P)) ∧
    (normalizationAlgebraMap k P).Finite ∧
    (∀ x : FractionRing (MonoidAlgebra k (GrothendieckGroup P)),
      (normalizationSaturatedFractionMap k P).IsIntegralElem x →
        x ∈ Set.range (normalizationSaturatedFractionMap k P)) := by
  sorry

end MonoidAlgebra
