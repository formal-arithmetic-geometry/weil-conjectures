/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# The separable closure at a pointed etale localization
Source: Stacks Project, Algebra, Tag 04GW.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given residue embedding makes K a separable closure over the etale localization.
Source: Stacks Project, Algebra, Tag 04GW (lemma-strict-henselization-different).
(blueprint: lem-sc-etale-localization-separable-closure).

Proof: Write etaR:R to kappa(R) and etaA:A to kappa(A) for the canonical residue maps,
and gamma=etaA composed with B to A composed with alpha. The triple compatibility
and hchi identify chiA composed with gamma with the original embedding composed with
etaR. Since chiA is injective, ker(etaR) is contained in ker(gamma). Since R is local,
etaR is surjective: use its canonical isomorphism with the ideal residue field, for
which the residue map at a maximal ideal is surjective. Descend gamma through etaR
using RingHom.liftOfSurjective. This defines j:kappa(R) to kappa(A), determined uniquely
by j composed with etaR=gamma. Surjectivity of etaR proves chiA composed with j equals
the original embedding into K, giving a scalar tower. K is separably closed by its
original separable-closure structure and separable over the middle field by separability
in towers. These are exactly the two separable-closure conditions. No finite-extension
argument or henselization is needed. -/
theorem etale_localization_separable_closure
    (R : CommRingCat.{u}) [IsLocalRing R]
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField (IsLocalRing.closedPoint R)) K]
    [IsSepClosure ((Spec R).residueField (IsLocalRing.closedPoint R)) K]
    (t : EtaleResidueTriples R (IsLocalRing.closedPoint R) K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField (IsLocalRing.closedPoint R)) K)))
    (A : CommRingCat.{u}) [Algebra t.B A] [IsLocalization.AtPrime A t.q.asIdeal]
    [IsLocalRing A]
    (χA : (Spec A).residueField (IsLocalRing.closedPoint A) ⟶ CommRingCat.of K)
    (hχA : CommRingCat.ofHom (algebraMap t.B A) ≫ (ΓSpecIso A).inv ≫
      (Spec A).Γevaluation (IsLocalRing.closedPoint A) ≫ χA =
      (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ)
 :
    letI : Algebra ((Spec A).residueField (IsLocalRing.closedPoint A)) K :=
      χA.hom.toAlgebra
    IsSepClosure ((Spec A).residueField (IsLocalRing.closedPoint A)) K := by
  classical
  let p := IsLocalRing.closedPoint R
  let kR := (Spec R).residueField p
  let kA := (Spec A).residueField (IsLocalRing.closedPoint A)
  let ηR : R →+* kR := ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p).hom
  let ηA : A →+* kA :=
    ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation (IsLocalRing.closedPoint A)).hom
  let γ : R →+* kA := ηA.comp ((algebraMap t.B A).comp t.α.hom)
  have hcompat : χA.hom.comp γ = (algebraMap kR K).comp ηR := by
    change (χA.hom.comp (ηA.comp (algebraMap t.B A))).comp t.α.hom = _
    have hχ : χA.hom.comp (ηA.comp (algebraMap t.B A)) =
        ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom :=
      congrArg CommRingCat.Hom.hom hχA
    rw [hχ]
    exact congrArg CommRingCat.Hom.hom t.compatible
  have hsurj : Function.Surjective ηR := by
    let e := Spec.residueFieldIso R p
    have he : e.inv.hom.comp (algebraMap R p.asIdeal.ResidueField) = ηR :=
      congrArg CommRingCat.Hom.hom (Spec.algebraMap_residueFieldIso_inv R p)
    have : p.asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
    intro x
    obtain ⟨y, hy⟩ := e.symm.commRingCatIsoToRingEquiv.surjective x
    obtain ⟨r, hr⟩ := p.asIdeal.algebraMap_residueField_surjective y
    refine ⟨r, ?_⟩
    exact (DFunLike.congr_fun he r).symm.trans ((congrArg e.inv.hom hr).trans hy)
  have hker : RingHom.ker ηR ≤ RingHom.ker γ := by
    intro r hr
    change γ r = 0
    apply χA.hom.injective
    have h := DFunLike.congr_fun hcompat r
    change χA.hom (γ r) = algebraMap kR K (ηR r) at h
    exact h.trans (by rw [RingHom.mem_ker.mp hr, map_zero, map_zero])
  let j : kR →+* kA := ηR.liftOfSurjective hsurj ⟨γ, hker⟩
  have hj : j.comp ηR = γ := ηR.liftOfSurjective_comp hsurj ⟨γ, hker⟩
  have htower : χA.hom.comp j = algebraMap kR K := by
    ext x
    obtain ⟨r, rfl⟩ := hsurj x
    exact (congrArg χA.hom (DFunLike.congr_fun hj r)).trans
      (DFunLike.congr_fun hcompat r)
  let : Algebra kR kA := j.toAlgebra
  let : Algebra kA K := χA.hom.toAlgebra
  let : IsScalarTower kR kA K := IsScalarTower.of_algebraMap_eq' htower.symm
  exact ⟨IsSepClosure.sep_closed kR,
    Algebra.isSeparable_tower_top_of_isSeparable kR kA K⟩

end AlgebraicGeometry.Scheme
