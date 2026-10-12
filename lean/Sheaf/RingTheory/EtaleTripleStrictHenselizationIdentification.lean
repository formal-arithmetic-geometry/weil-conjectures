/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.RingTheory.StrictHenselizationTriples
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.MapIntoHenselianColimit

/-!
# Strict henselization at an etale triple

Source: Stacks Project, Tags 06LJ, 04GW and 04GP
(blueprint: lem-sc-etale-triple-strict-henselization-identification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Strict henselization of the localization of a pointed etale algebra agrees canonically
with the original strict henselization, including the maximal ideal and its completion.
Source: Stacks Project, Tags 06LJ (proof of (c)), 04GW and 04GP
(blueprint: lem-sc-etale-triple-strict-henselization-identification).

The cocones and their structural and residue maps specify the two strict henselizations
as in `strictHenselization_triples`. The equality `hχA` specifies the residue embedding
induced by the triple on the localization `A`. No chosen strict henselization is required.

Proof:
1. Apply lem-weil-pbc-strict-henselization-triples to R and A. The field K is also a
separable closure of the residue field at the triple, since that field is finite separable
over the residue field of R. The two colimits are strictly henselian with residue field K.
2. The preimage of the maximal ideal of C in S is q, so S → C factors uniquely through
A = S_q by localization, using the preimage clause of that lemma.
3. Apply lem-weil-pbc-map-into-henselian-colimit over A to obtain D → C and over R to
obtain C → D, in both cases with residue map the identity on K.
4. Uniqueness over R makes their composite on C the identity. Uniqueness for the etale
algebra S and then localization gives compatibility on A; uniqueness over A makes the
composite on D the identity. This also gives uniqueness of the comparison preserving S
and the maps to K.
5. Locality identifies qD with the maximal ideal mC of C (the maximal ideal of C is mC by
lem-weil-pbc-strict-henselization-triples). All powers are identified, so the
induced quotient isomorphisms give the isomorphism of inverse limits, using
 def-weil-pbc-adic-completion. Its projections send the class of a to the class of e(a).
-/
theorem etaleTriple_strictHenselization_identification
    (R : CommRingCat.{u}) [IsLocalRing R]
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField (IsLocalRing.closedPoint R)) K]
    [IsSepClosure ((Spec R).residueField (IsLocalRing.closedPoint R)) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R (IsLocalRing.closedPoint R) K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField (IsLocalRing.closedPoint R)) K))))
    (hc : IsColimit c)
    (ρ : R ⟶ c.pt) (ψ : c.pt →+* K)
    (hρ : ∀ s, s.α ≫ c.ι.app s = ρ)
    (hψ : ∀ s, ψ.comp (c.ι.app s).hom =
      ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ).hom)
    (t : EtaleResidueTriples R (IsLocalRing.closedPoint R) K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField (IsLocalRing.closedPoint R)) K)))
    (A : CommRingCat.{u}) [Algebra t.B A] [IsLocalization.AtPrime A t.q.asIdeal]
    [IsLocalRing A]
    (χA : (Spec A).residueField (IsLocalRing.closedPoint A) ⟶ CommRingCat.of K)
    (hχA : CommRingCat.ofHom (algebraMap t.B A) ≫ (ΓSpecIso A).inv ≫
      (Spec A).Γevaluation (IsLocalRing.closedPoint A) ≫ χA =
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ)
    (d : Cocone (etaleResidueTriplesRingDiagram A (IsLocalRing.closedPoint A) K χA))
    (hd : IsColimit d) (δ : A ⟶ d.pt) (ψD : d.pt →+* K)
    (hδ : ∀ s, s.α ≫ d.ι.app s = δ)
    (hψD : ∀ s, ψD.comp (d.ι.app s).hom =
      ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ).hom) :
    ∃! e : d.pt ≃+* c.pt,
      e.toRingHom.comp (δ.hom.comp (algebraMap t.B A)) = (c.ι.app t).hom ∧
      ψ.comp e.toRingHom = ψD ∧
      (t.q.asIdeal.map (δ.hom.comp (algebraMap t.B A))).map e.toRingHom =
        (IsLocalRing.maximalIdeal R).map ρ.hom ∧
      ∃ ê : AdicCompletion (t.q.asIdeal.map (δ.hom.comp (algebraMap t.B A))) d.pt ≃+*
          AdicCompletion ((IsLocalRing.maximalIdeal R).map ρ.hom) c.pt,
        ∀ (n : ℕ) (x : AdicCompletion
            (t.q.asIdeal.map (δ.hom.comp (algebraMap t.B A))) d.pt) (a : d.pt),
          AdicCompletion.evalₐ (t.q.asIdeal.map (δ.hom.comp (algebraMap t.B A))) n x =
            Ideal.Quotient.mk ((t.q.asIdeal.map (δ.hom.comp (algebraMap t.B A))) ^ n) a →
          AdicCompletion.evalₐ ((IsLocalRing.maximalIdeal R).map ρ.hom) n (ê x) =
            Ideal.Quotient.mk (((IsLocalRing.maximalIdeal R).map ρ.hom) ^ n) (e a) := by
  sorry

end AlgebraicGeometry.Scheme
