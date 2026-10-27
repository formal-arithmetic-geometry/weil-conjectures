/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations
import Sheaf.RingTheory.PrimePairColimitIndEtaleModel
import Sheaf.RingTheory.InitialHenselianColimitComparison
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.RingTheory.StrictHenselizationFiniteLifts
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.MapIntoHenselianColimit

/-!
# Local embeddings into a separable normalization

Source: Stacks Project, Fundamental Groups, Tags 0BSD and 0BSQ; Algebra, Tag 08HR
(blueprint: lem-dl-a1-separable-normalization-local-embeddings).
The pointed-algebra presentation specifies the strict henselization and its residue map.
-/

@[expose] public section
set_option autoImplicit false

universe u

namespace Algebra

/-- Compatible embeddings of the ordinary and strict henselizations in the localization
of the integral closure in a separable closure.
Source: Stacks Project, Tags 0BSD, 0BSQ and 08HR
(blueprint: lem-dl-a1-separable-normalization-local-embeddings).

Proof: (1) The integral closure is a normal domain with fraction field Omega by
lem-weil-pbc-integral-closure-algebraic-extension-normal; localize using
lem-weil-pbc-localization-normal-domain. The quotient-localization residue isomorphism
sends b mod q to the residue of b/1. (2) Reduce the monic equations modulo q to obtain
algebraicity of the residue extension. Apply lem-weil-pbc-gabber-quotient-localizations
with zero ideal to obtain strict henselianity. (3) Use
lem-trf-prime-pair-colimit-ind-etale-model and
lem-trf-initial-henselian-colimit-comparison to identify the specified ordinary
henselization with its ind-etale model. The normality and injectivity follow from
lem-weil-pbc-etale-colimit-normal-local-domain, using
lem-weil-pbc-localization-normal-domain to check normality of the base ring.
(4) Apply lem-wf-strict-henselization-finite-lifts to identify the specified pointed
strict henselization with the finite-local-etale-lift colimit over H. Its locality,
residue field and strict henselianity follow from
lem-wf-finite-local-lift-colimit-structure. The canonical H-map is local; normality
and injectivity follow again from lem-weil-pbc-etale-colimit-normal-local-domain.
Composition is ind-etale by lem-weil-pbc-ind-etale-stability.
(5) Use lem-weil-pbc-separable-extension-embeds-separably-closed for the residue embedding.
(6) The henselization universal property gives the unique local map h. Apply
lem-weil-pbc-map-into-henselian-colimit over H to lift each residue embedding uniquely.
Any local A-map restricts to h, so uniqueness holds among all compatible local maps.
(7) The final clause of lem-dl-a1-ind-etale-domain-generic-field makes both composites
into Omega injective, hence both local maps injective. Their compatibility gives
all the asserted embeddings. No Noetherian hypothesis is needed. -/
theorem separableNormalization_local_embeddings
    (A K Ω H ks R : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra A Ω] [IsScalarTower A K Ω]
    (q : Ideal (integralClosure A Ω)) [q.IsMaximal]
    (hq : q.comap (algebraMap A (integralClosure A Ω)) = IsLocalRing.maximalIdeal A)
    [CommRing H] [HenselianLocalRing H] [Algebra A H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    [IsScalarTower A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    (hH : IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H)
    [Field ks] [Algebra (IsLocalRing.ResidueField A) ks]
    [IsSepClosure (IsLocalRing.ResidueField A) ks]
    [Algebra A ks] [IsScalarTower A (IsLocalRing.ResidueField A) ks]
    [CommRing R] [Algebra A R]
    (P : StrictHenselizationPresentationIn.{u, u} A ks R) :
    IsDomain (integralClosure A Ω) ∧ IsIntegrallyClosed (integralClosure A Ω) ∧
    IsFractionRing (integralClosure A Ω) Ω ∧
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) ∧
    (∃ (_ : Algebra (Localization.AtPrime q) Ω),
      IsScalarTower (integralClosure A Ω) (Localization.AtPrime q) Ω ∧
      IsFractionRing (Localization.AtPrime q) Ω) ∧
    IsStrictlyHenselianLocalRing (Localization.AtPrime q) ∧
    IsLocalHom (algebraMap A (Localization.AtPrime q)) ∧
    (∃ e : (integralClosure A Ω ⧸ q) ≃+*
        IsLocalRing.ResidueField (Localization.AtPrime q),
      e.toRingHom.comp (Ideal.Quotient.mk q) =
        (IsLocalRing.residue (Localization.AtPrime q)).comp
          (algebraMap (integralClosure A Ω) (Localization.AtPrime q))) ∧
    IsDomain H ∧ IsIntegrallyClosed H ∧
    IsLocalHom (algebraMap A H) ∧ Function.Injective (algebraMap A H) ∧
    RingHom.IndEtaleAcrossUniverses (algebraMap A H) ∧
    (∃ eH : IsLocalRing.ResidueField H ≃+* IsLocalRing.ResidueField A,
      eH.toRingHom.comp ((IsLocalRing.residue H).comp (algebraMap A H)) =
        IsLocalRing.residue A) ∧
    ∃ (_ : IsLocalRing R) (_ : Algebra H R), IsScalarTower A H R ∧
      IsDomain R ∧ IsIntegrallyClosed R ∧
      IsLocalHom (algebraMap H R) ∧ Function.Injective (algebraMap H R) ∧
      RingHom.IndEtaleAcrossUniverses (algebraMap H R) ∧
      (∃ eR : IsLocalRing.ResidueField R ≃+* ks,
        eR.toRingHom.comp (IsLocalRing.residue R) = P.residueMap) ∧
      ∃ (_ : Algebra (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q))),
        IsScalarTower A (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q)) ∧
        Algebra.IsAlgebraic (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q)) ∧
        Nonempty (ks →ₐ[IsLocalRing.ResidueField A]
          IsLocalRing.ResidueField (Localization.AtPrime q)) ∧
        ∃ h : H →ₐ[A] Localization.AtPrime q,
          IsLocalHom h.toRingHom ∧ Function.Injective h ∧
          (∀ h' : H →ₐ[A] Localization.AtPrime q, IsLocalHom h'.toRingHom → h' = h) ∧
          ∀ j : ks →ₐ[IsLocalRing.ResidueField A]
              IsLocalRing.ResidueField (Localization.AtPrime q),
            ∃ i : R →ₐ[A] Localization.AtPrime q,
              IsLocalHom i.toRingHom ∧ Function.Injective i ∧
              i.toRingHom.comp (algebraMap H R) = h.toRingHom ∧
              (IsLocalRing.residue (Localization.AtPrime q)).comp i.toRingHom =
                j.toRingHom.comp P.residueMap ∧
              ∀ i' : R →ₐ[A] Localization.AtPrime q, IsLocalHom i'.toRingHom →
                (IsLocalRing.residue (Localization.AtPrime q)).comp i'.toRingHom =
                  j.toRingHom.comp P.residueMap → i' = i := by
  sorry

end Algebra
