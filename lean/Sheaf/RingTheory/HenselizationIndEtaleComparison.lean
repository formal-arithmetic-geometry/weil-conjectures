/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import WeilConjectures.RingTheory.EtaleResidueTriplesStrictHenselization

/-!
# Recognition over a local ring and its henselization

Source: Stacks Project, Algebra, Tag 0BSL (remark-construct-sh-from-h), with Tags
04GN, 0BSI, 08HR, 08HT and 04GW
(blueprint: lem-wf-henselization-ind-etale-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Algebra

/-- Recognition of the pointed strict henselization over both a local ring and its
ordinary henselization. The two cocones are arbitrary universal ring cocones of
residue triples; their algebra structures and residue maps are specified on every leg.
The residue-field isomorphism `e` is the identification of the henselization residue
field with that of the original ring, and `hK` transports the fixed embedding into `K`.
The last clause characterizes the canonical local map by its universal property,
without choosing a map from a bare existence assertion.

Source: Stacks Project, Algebra, Tag 0BSL (remark-construct-sh-from-h), final sentences,
with Tags 04GN, 0BSI, 08HR, 08HT and 04GW
(blueprint: lem-wf-henselization-ind-etale-comparison).

Proof:
1. At the maximal ideal, localization of `A` is canonically `A`, since every
   denominator is a unit. Apply lem-trf-henselization-prime-ind-etale to see that
   `A → H` is ind-etale. Compose with `H → C` using lem-weil-pbc-ind-etale-stability.
   Both structural maps are local, so their composite is local.
2. Transport the separable closure across `e`. Over each of `A` and `H`, apply
   lem-weil-pbc-strict-henselization-triples. The triple colimit is henselian local,
   has a filtered etale presentation, and its pointing map is surjective with
   maximal-ideal kernel and the prescribed composite from the base.
3. Apply lem-weil-pbc-map-into-henselian-colimit in both directions between `C`
   and each triple colimit, with the identity map on their residue field `K`.
   The maximal ideals contract to the base maximal ideal; the prescribed base
   maps give residue compatibility. Uniqueness makes both inverse composites
   identities. Any residue-preserving algebra isomorphism is local, hence is
   the same map by that uniqueness.
4. Apply lem-sc-etale-triples-colimit-is-strict-henselization to each colimit.
   Use the algebra isomorphisms of step 3 to transport the pointed universal
   cocones to `C`. Their induced residue maps are `q` by the compatibility in
   step 3, giving the recorded StrictHenselizationPresentationIn witnesses.
5. By step 2 the colimit over `A` is henselian local and its base map is local.
   The universal property in def-weil-pbc-henselization-at-prime gives the unique
   local extension from `H`. The comparison composed with `H → C` is local and
   extends the same base map, so it equals this extension.
-/
theorem henselization_indEtale_comparison
    (A H C K : Type u) [CommRing A] [IsLocalRing A]
    [CommRing H] [HenselianLocalRing H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    [Algebra A H]
    [IsScalarTower A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    (hH : IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H)
    (e : IsLocalRing.ResidueField H ≃+* IsLocalRing.ResidueField A)
    (he : (e.toRingHom.comp (IsLocalRing.residue H)).comp (algebraMap A H) =
      IsLocalRing.residue A)
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [Algebra (IsLocalRing.ResidueField H) K]
    (hK : algebraMap (IsLocalRing.ResidueField H) K =
      (algebraMap (IsLocalRing.ResidueField A) K).comp e.toRingHom)
    [Algebra H K] [IsScalarTower H (IsLocalRing.ResidueField H) K]
    [CommRing C] [HenselianLocalRing C]
    [Algebra H C] [Algebra A C] [IsScalarTower A H C]
    (hlocal : IsLocalHom (algebraMap H C))
    (hind : RingHom.IndEtaleAcrossUniverses (algebraMap H C))
    (q : C →+* K) (hqsurj : Function.Surjective q)
    (hqker : RingHom.ker q = IsLocalRing.maximalIdeal C)
    (hq : q.comp (algebraMap H C) = algebraMap H K)
    (χA : (Spec (CommRingCat.of A)).residueField (IsLocalRing.closedPoint A) ⟶
      CommRingCat.of K)
    (hχA : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec (CommRingCat.of A)).Γevaluation (IsLocalRing.closedPoint A) ≫ χA =
      CommRingCat.ofHom (algebraMap A K))
    (χH : (Spec (CommRingCat.of H)).residueField (IsLocalRing.closedPoint H) ⟶
      CommRingCat.of K)
    (hχH : (Scheme.ΓSpecIso (CommRingCat.of H)).inv ≫
      (Spec (CommRingCat.of H)).Γevaluation (IsLocalRing.closedPoint H) ≫ χH =
      CommRingCat.ofHom (algebraMap H K))
    (cA : Cocone (Scheme.etaleResidueTriplesRingDiagram (CommRingCat.of A)
      (IsLocalRing.closedPoint A) K χA)) (hcA : IsColimit cA)
    (cH : Cocone (Scheme.etaleResidueTriplesRingDiagram (CommRingCat.of H)
      (IsLocalRing.closedPoint H) K χH)) (hcH : IsColimit cH)
    [Algebra A cA.pt] [Algebra H cH.pt]
    (hρA : ∀ t, t.α ≫ cA.ι.app t = CommRingCat.ofHom (algebraMap A cA.pt))
    (hρH : ∀ t, t.α ≫ cH.ι.app t = CommRingCat.ofHom (algebraMap H cH.pt))
    (qA : cA.pt →+* K) (qH : cH.pt →+* K)
    (hqA : ∀ t, qA.comp (cA.ι.app t).hom =
      ((Scheme.ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (hqH : ∀ t, qH.comp (cH.ι.app t).hom =
      ((Scheme.ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    IsLocalHom (algebraMap A C) ∧
      RingHom.IndEtaleAcrossUniverses (algebraMap A C) ∧
      (∃! aA : C ≃ₐ[A] cA.pt, qA.comp aA.toRingHom = q) ∧
      (∃! aH : C ≃ₐ[H] cH.pt, qH.comp aH.toRingHom = q) ∧
      (∃ P : StrictHenselizationPresentationIn.{u, u} A K C, P.residueMap = q) ∧
      (∃ sH : IsSepClosure (IsLocalRing.ResidueField H) K,
        ∃ P : @StrictHenselizationPresentationIn.{u, u} H K C _ _ _ _ sH _ _ _ _,
          @StrictHenselizationPresentationIn.residueMap.{u, u}
            H K C _ _ _ _ sH _ _ _ _ P = q) ∧
      (∀ aA : C ≃ₐ[A] cA.pt, qA.comp aA.toRingHom = q →
        IsLocalHom (aA.toRingHom.comp (algebraMap H C)) ∧
        ∀ j : H →+* cA.pt, IsLocalHom j →
          j.comp (algebraMap A H) = algebraMap A cA.pt →
          aA.toRingHom.comp (algebraMap H C) = j) := by
  sorry

end Algebra
