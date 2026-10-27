/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.RingTheory.Etale.LocalDimension
import WeilConjectures.RingTheory.Etale.IntegrallyClosedLocalization
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent
import Sheaf.RingTheory.FaithfullyFlatNormalRingDescent

/-!
# Local-ring invariants under an étale scheme morphism

Source: Stacks Project, More on Algebra, Tags 07QP and 0AH0; Algebra, Tags 033C and 033G.
This is the scheme-stalk assembly of these ring results
(blueprint: lem-sfb-etale-stalk-invariants).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem normalDomain_transport {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsDomain R ∧ IsIntegrallyClosed R) :
    IsDomain S ∧ IsIntegrallyClosed S := by
  obtain ⟨hD, hN⟩ := h
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

private theorem normalDomain_iff_localizations (R : Type u) [CommRing R] [IsLocalRing R] :
    (IsDomain R ∧ IsIntegrallyClosed R) ↔
      ∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  constructor
  · rintro ⟨hD, hN⟩ p hp
    let : IsDomain R := hD
    let : IsIntegrallyClosed R := hN
    exact ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
        p.primeCompl_le_nonZeroDivisors⟩
  · intro h
    let p := IsLocalRing.maximalIdeal R
    let e := (IsLocalization.atUnits R p.primeCompl (S := Localization.AtPrime p)
      (fun x hx ↦ by
        change ¬ ¬ IsUnit x at hx
        exact not_not.mp hx)).toRingEquiv
    exact normalDomain_transport e.symm (h p)

private def ringInvariants (R S : Type u) [CommRing R] [CommRing S] : Prop :=
  ringKrullDim R = ringKrullDim S ∧
    (IsRegularLocalRing R ↔ IsRegularLocalRing S) ∧
    ((IsDomain R ∧ IsIntegrallyClosed R) ↔ (IsDomain S ∧ IsIntegrallyClosed S))

private theorem ringInvariants_transport {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (eR : R ≃+* R') (eS : S ≃+* S') (h : ringInvariants R S) :
    ringInvariants R' S' := by
  refine ⟨eR.ringKrullDim.symm.trans (h.1.trans eS.ringKrullDim), ?_, ?_⟩
  · constructor
    · intro hr
      have : IsRegularLocalRing R := IsRegularLocalRing.of_ringEquiv eR.symm
      have : IsRegularLocalRing S := h.2.1.mp this
      exact IsRegularLocalRing.of_ringEquiv eS
    · intro hs
      have : IsRegularLocalRing S := IsRegularLocalRing.of_ringEquiv eS.symm
      have : IsRegularLocalRing R := h.2.1.mpr this
      exact IsRegularLocalRing.of_ringEquiv eR
  · exact ⟨fun hr ↦ normalDomain_transport eS
        (h.2.2.mp (normalDomain_transport eR.symm hr)),
      fun hs ↦ normalDomain_transport eR
        (h.2.2.mpr (normalDomain_transport eS.symm hs))⟩

private theorem ringInvariants_respectsIso :
    RingHom.RespectsIso (fun {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S) ↦
      ringInvariants R S) := by
  constructor
  · intro R S T _ _ _ f e h
    exact ringInvariants_transport (RingEquiv.refl R) e h
  · intro R S T _ _ _ f e h
    exact ringInvariants_transport e.symm (RingEquiv.refl T) h

private theorem ringInvariants_localization {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (q : Ideal S) [q.IsPrime] :
    ringInvariants (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) := by
  let A := Localization.AtPrime (q.comap f)
  let B := Localization.AtPrime q
  let g : A →+* B := Localization.localRingHom (q.comap f) q f rfl
  let : Algebra A B := g.toAlgebra
  have hflat : g.Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1.localRingHom q (q.comap f) rfl
  have : Module.Flat A B := hflat
  have : IsLocalHom (algebraMap A B) := show IsLocalHom g from inferInstance
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨hf.ringKrullDim_localization_eq f q, ?_, ?_⟩
  · constructor
    · intro hA
      let : Algebra R S := f.toAlgebra
      have : Algebra.Etale R S := hf
      exact IsRegularLocalRing.localization_of_etale_of_comap (R := R) q hA
    · intro hB
      have : IsRegularRing B :=
        (IsRegularLocalRing.localization_at_prime_and_isRegularRing
          (IsLocalRing.maximalIdeal B)).2
      have : IsRegularRing A := IsRegularRing.of_faithfullyFlat A B
      exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
  · constructor
    · intro hA
      let : Algebra R S := f.toAlgebra
      have : Algebra.Etale R S := hf
      exact Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap q hA
    · intro hB
      exact (normalDomain_iff_localizations A).mpr
        (Algebra.normal_ring_of_faithfullyFlat A B
          ((normalDomain_iff_localizations B).mp hB))

/-- An étale morphism induces a faithfully flat local homomorphism on stalks, preserving
Krull dimension and reflecting both regular local rings and integrally closed domains.
Neither scheme is assumed globally Noetherian. No comparison of residue or fraction fields
is asserted.

Source: Stacks Project, More on Algebra, Tags 07QP and 0AH0; Algebra, Tags 033C and 033G
(blueprint: lem-sfb-etale-stalk-invariants).

Proof:
1. The stalk map is flat by def-weil-etale-morphism and def-weil-flat-morphism, and local
   by def-weil-locally-ringed-space-morphism. Apply
   lem-weil-pbc-flat-local-hom-faithfully-flat to obtain faithful flatness.
2. Choose affine étale charts Spec S -> Spec R through the point. Restriction to an open
   preserves stalks. By lem-weil-pbc-spec-map-stalk-localization the map is R_p -> S_q,
   where p is the contraction of q. Apply lem-sc-etale-local-dimension to obtain dimension
   equality, including infinite Krull dimension.
3. Write A = R_p and C = (R minus p)^(-1)S. The fraction formulas identify C with
   A tensor_R S and its localization at the prime induced by q with S_q = B, compatibly
   with the stalk map. Use lem-sbc-finite-affine-tensor-base-change in the one-component
   case and lem-weil-pbc-etale-base-change-finite-limits to see that Spec C -> Spec A
   is étale. By lem-weil-pbc-etale-ring-map-iff-etale-affine and
   def-weil-pbc-smooth-ring-map the ring map A -> C is smooth.
4. If A is regular local, lem-weil-pbc-regular-local-localization makes A regular.
   By lem-weil-pbc-regular-ring-smooth-ascent, C is regular. By
   lem-weil-pbc-localization-of-regular-ring, C localized at q is regular. Its localization
   at the maximal ideal is itself, so B is regular local, by def-weil-regular-scheme.
5. If B is regular local, lem-weil-pbc-regular-local-localization makes B regular.
   Faithful flatness and lem-weil-pbc-regular-ring-faithfully-flat-descent make A regular.
   Localizing at its maximal ideal, which does not change A, makes A regular local.
6. If A is an integrally closed domain, lem-weil-pbc-localization-normal-domain makes
   A normal in the sense of def-weil-pbc-normal-ring. Then
   lem-weil-pbc-etale-over-normal-ring-normal makes C normal, so B is an integrally closed
   domain. Conversely, if B is an integrally closed domain, localization makes B normal;
   lem-sfb-faithfully-flat-normal-ring-descent makes A normal by step 1. Its localization
   at the maximal ideal is itself, so A is an integrally closed domain. -/
theorem etale_stalk_invariants {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] (u : U) :
    (e.stalkMap u).hom.FaithfullyFlat ∧
      ringKrullDim (X.presheaf.stalk (e u)) = ringKrullDim (U.presheaf.stalk u) ∧
      (IsRegularLocalRing (X.presheaf.stalk (e u)) ↔
        IsRegularLocalRing (U.presheaf.stalk u)) ∧
      ((IsDomain (X.presheaf.stalk (e u)) ∧ IsIntegrallyClosed (X.presheaf.stalk (e u))) ↔
        (IsDomain (U.presheaf.stalk u) ∧ IsIntegrallyClosed (U.presheaf.stalk u))) := by
  have hff : (e.stalkMap u).hom.FaithfullyFlat := by
    algebraize [(e.stalkMap u).hom]
    have : Module.Flat (X.presheaf.stalk (e u)) (U.presheaf.stalk u) := Flat.stalkMap e u
    have : IsLocalHom (algebraMap (X.presheaf.stalk (e u))
        (U.presheaf.stalk u)) := e.toLRSHom.prop u
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨hff, ?_⟩
  exact HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale)
    ringInvariants_respectsIso (fun f hf q _ ↦ ringInvariants_localization f hf q)
    inferInstance u

end AlgebraicGeometry
