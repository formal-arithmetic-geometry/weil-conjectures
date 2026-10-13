/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module
public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
import Sheaf.RingTheory.StrictHenselizationTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.MapIntoHenselianColimit

/-!
# Comparison of pointed etale strict henselizations

Source: Stacks Project, Algebra, Tags 04GW, 04GP, and 08HR.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The comparison of the two pointed colimits, before transporting ideals or completions.
Source: Stacks Project, Algebra, Tags 04GW and 04GP, using Tag 08HR.
(blueprint: lem-sc-strict-henselization-comparison).

Proof: Apply the strict-henselization triples theorem to the base R. The embedding
chiA equips K with a separable-closure structure over the residue field of A: that
residue field is the finite separable extension of the residue field of R determined
by t. Apply the triples theorem over A as well, transporting its conclusions to the
specified colimit cocones by uniqueness of colimits. Both colimit rings are therefore
henselian local, and their residue maps are surjective with kernel the maximal ideal.
The map t.B to c.pt inverts every element outside t.q, since its residue in K is
nonzero; extend it uniquely to A by localization. Apply the henselian-colimit mapping
lemma over A to obtain f from d.pt to c.pt with prescribed residue map. Apply it over
R to obtain g from c.pt to d.pt, using R to A to d.pt as its R-algebra
structure. Here the source c.pt is ind-etale over R; the target d.pt need only
be henselian local. The composite on c.pt is the identity by uniqueness over R.
On t.B, the maps from A through g and directly into d.pt are equal by the
single-etale uniqueness in Tag 08HQ; localization gives equality on A. Uniqueness
over A now makes the other composite the identity. Bundle f and g as a ring
equivalence. Any other equivalence satisfying the displayed compatibilities agrees
on A by localization and has the same residue map, so uniqueness over A identifies
it with f. The assertion does not transport any ideal or adic completion. -/
theorem strictHenselization_comparison
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
      ψ.comp e.toRingHom = ψD := by
  sorry

end AlgebraicGeometry.Scheme
