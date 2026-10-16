/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import Sheaf.RingTheory.StrictHenselizationTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.EtaleHenselianRingLift
import Sheaf.RingTheory.EtaleLocalizationSeparableClosure

/-!
# Comparison of pointed etale strict henselizations

Source: Stacks Project, Algebra, Tags 04GW, 04GP, and 08HR.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointed_colimit_properties
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c) (ψ : c.pt →+* K)
    (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    ∃ _h : HenselianLocalRing c.pt,
      Function.Surjective ψ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal c.pt := by
  classical
  obtain ⟨_, c₀, ⟨hc₀⟩, hlocal, _, ψ₀, _, hψ₀, hsurj, _, _, _, _, hstrict⟩ :=
    strictHenselization_triples R p K
  let := hlocal
  let := hstrict
  let e := hc.coconePointUniqueUpToIso hc₀
  have he : ψ₀.comp e.hom.hom = ψ := by
    have he' : e.hom ≫ CommRingCat.ofHom ψ₀ = CommRingCat.ofHom ψ := by
      apply hc.hom_ext
      intro t
      calc
        _ = (c.ι.app t ≫ e.hom) ≫ CommRingCat.ofHom ψ₀ :=
          (Category.assoc _ _ _).symm
        _ = c₀.ι.app t ≫ CommRingCat.ofHom ψ₀ := congrArg
          (fun f ↦ f ≫ CommRingCat.ofHom ψ₀)
          (hc.comp_coconePointUniqueUpToIso_hom hc₀ t)
        _ = c.ι.app t ≫ CommRingCat.ofHom ψ := by
          apply CommRingCat.hom_ext
          exact (hψ₀ t).trans (hψ t).symm
    exact congrArg CommRingCat.Hom.hom he'
  let : HenselianLocalRing c.pt :=
    HenselianLocalRing.of_ringEquiv e.symm.commRingCatIsoToRingEquiv
  have hs : Function.Surjective ψ := by
    rw [← he]
    exact hsurj.comp e.commRingCatIsoToRingEquiv.surjective
  exact ⟨inferInstance, hs, IsLocalRing.ker_eq_maximalIdeal ψ hs⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pointed_colimit_lift
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) (hc : IsColimit c)
    (ρ : R ⟶ c.pt) (hρ : ∀ t, t.α ≫ c.ι.app t = ρ)
    (ψ : c.pt →+* K) (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
    (S : CommRingCat.{u}) [HenselianLocalRing S]
    (β : R ⟶ S) (ε : S →+* K) (hs : Function.Surjective ε)
    (hk : RingHom.ker ε = IsLocalRing.maximalIdeal S)
    (hβ : ε.comp β.hom = ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ).hom) :
    ∃! f : c.pt →+* S, f.comp ρ.hom = β.hom ∧ ε.comp f = ψ := by
  classical
  have lifts (t : EtaleResidueTriples R p K χ) :
      ∃! f : t.B →+* S, f.comp t.α.hom = β.hom ∧
        ε.comp f = ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom := by
    apply etale_henselian_ring_lift R t.B S t.α t.etale β K ε hs hk
    exact (congrArg CommRingCat.Hom.hom t.compatible).trans hβ.symm
  choose f hf hu using lifts
  let d : Cocone (etaleResidueTriplesRingDiagram R p K χ) :=
    { pt := S
      ι :=
        { app := fun t ↦ CommRingCat.ofHom (f t)
          naturality := by
            intro t s a
            apply CommRingCat.hom_ext
            change (f s).comp a.hom.right.left.hom = f t
            apply hu t
            constructor
            · rw [RingHom.comp_assoc]
              have ha := congrArg Over.Hom.left (Under.w a.hom)
              change t.α ≫ a.hom.right.left = s.α at ha
              rw [← CommRingCat.hom_comp, ha]
              exact (hf s).1
            · rw [← RingHom.comp_assoc, (hf s).2]
              exact congrArg CommRingCat.Hom.hom (Over.w a.hom.right) } }
  let g := (hc.desc d).hom
  have hg (t : EtaleResidueTriples R p K χ) :
      g.comp (c.ι.app t).hom = f t := congrArg CommRingCat.Hom.hom (hc.fac d t)
  let t₀ : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  have ht₀ : c.ι.app t₀ = ρ := by simpa [t₀] using hρ t₀
  have hbase : g.comp ρ.hom = β.hom := by
    rw [← ht₀, hg]
    simpa [t₀] using (hf t₀).1
  have hred : ε.comp g = ψ := by
    have h : hc.desc d ≫ CommRingCat.ofHom ε = CommRingCat.ofHom ψ := by
      apply hc.hom_ext
      intro t
      apply CommRingCat.hom_ext
      change (ε.comp g).comp (c.ι.app t).hom = ψ.comp (c.ι.app t).hom
      rw [RingHom.comp_assoc, hg, (hf t).2, hψ t]
    exact congrArg CommRingCat.Hom.hom h
  refine ⟨g, ⟨hbase, hred⟩, ?_⟩
  intro g' hg'
  have h : CommRingCat.ofHom g' = hc.desc d := by
    apply hc.hom_ext
    intro t
    apply CommRingCat.hom_ext
    change g'.comp (c.ι.app t).hom = g.comp (c.ι.app t).hom
    rw [hg]
    apply hu t
    constructor
    · rw [RingHom.comp_assoc, ← CommRingCat.hom_comp, hρ t]
      exact hg'.1
    · rw [← RingHom.comp_assoc, hg'.2, hψ t]
  exact congrArg CommRingCat.Hom.hom h

private theorem pointed_colimit_base
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ))
    (ρ : R ⟶ c.pt) (hρ : ∀ t, t.α ≫ c.ι.app t = ρ)
    (ψ : c.pt →+* K) (hψ : ∀ t, ψ.comp (c.ι.app t).hom =
      ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom) :
    ψ.comp ρ.hom = ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ).hom := by
  let t₀ : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  have ht₀ : c.ι.app t₀ = ρ := by simpa [t₀] using hρ t₀
  exact (congrArg (fun f ↦ ψ.comp f.hom) ht₀).symm.trans (hψ t₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison of the two pointed colimits, before transporting ideals or completions.
Source: Stacks Project, Algebra, Tags 04GW and 04GP, using Tag 08HR.
(blueprint: lem-sc-strict-henselization-comparison).

Proof: Apply the strict-henselization triples theorem to the base R. The embedding
chiA equips K with a separable-closure structure over the residue field of A:
descend the compatible residue map through the surjective residue map of the local
ring R, then apply separability in towers. Apply the triples theorem over A as well,
transporting its conclusions to the
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
  classical
  let χR := CommRingCat.ofHom (algebraMap
    ((Spec R).residueField (IsLocalRing.closedPoint R)) K)
  let : Algebra ((Spec A).residueField (IsLocalRing.closedPoint A)) K := χA.hom.toAlgebra
  have : IsSepClosure ((Spec A).residueField (IsLocalRing.closedPoint A)) K :=
    etale_localization_separable_closure R K t A χA hχA
  obtain ⟨hC, hsC, hkC⟩ := pointed_colimit_properties R _ K c hc ψ hψ
  let := hC
  obtain ⟨hD, hsD, hkD⟩ := pointed_colimit_properties A _ K d hd ψD hψD
  let := hD
  have hψρ := pointed_colimit_base R _ K χR c ρ hρ ψ hψ
  have hψδ := pointed_colimit_base A _ K χA d δ hδ ψD hψD
  have units (x : t.q.asIdeal.primeCompl) : IsUnit ((c.ι.app t).hom x.val) := by
    apply not_not.mp
    change (c.ι.app t).hom x.val ∉ IsLocalRing.maximalIdeal c.pt
    rw [← hkC, RingHom.mem_ker]
    have hx := DFunLike.congr_fun (hψ t) x.val
    change ψ ((c.ι.app t).hom x.val) = _ at hx
    have hn :
        ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom x.val ≠ 0 := by
      change t.φ.hom (((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q).hom x.val) ≠ 0
      rw [map_ne_zero]
      have hcanon := Spec.algebraMap_residueFieldIso_inv t.B t.q
      change CommRingCat.ofHom (algebraMap t.B t.q.asIdeal.ResidueField) ≫
        (Spec.residueFieldIso t.B t.q).inv =
          (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q at hcanon
      rw [← hcanon]
      change (Spec.residueFieldIso t.B t.q).inv.hom
        (algebraMap t.B t.q.asIdeal.ResidueField x.val) ≠ 0
      rw [map_ne_zero]
      exact fun h ↦ x.property ((Ideal.algebraMap_residueField_eq_zero).mp h)
    exact fun hz ↦ hn (hx.symm.trans hz)
  let βC : A →+* c.pt := IsLocalization.lift (S := A) units
  have hβC : βC.comp (algebraMap t.B A) = (c.ι.app t).hom :=
    IsLocalization.lift_comp units
  have hredC : ψ.comp βC =
      ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation (IsLocalRing.closedPoint A) ≫ χA).hom := by
    apply IsLocalization.ringHom_ext t.q.asIdeal.primeCompl
    rw [RingHom.comp_assoc, hβC, hψ t]
    exact (congrArg CommRingCat.Hom.hom hχA).symm
  obtain ⟨f, hf, huf⟩ := pointed_colimit_lift A _ K χA d hd δ hδ ψD hψD
    c.pt (CommRingCat.ofHom βC) ψ hsC hkC hredC
  change f.comp δ.hom = βC ∧ ψ.comp f = ψD at hf
  change ∀ f', f'.comp δ.hom = βC ∧ ψ.comp f' = ψD → f' = f at huf
  let βD : R ⟶ d.pt := t.α ≫ CommRingCat.ofHom (algebraMap t.B A) ≫ δ
  have hredD : ψD.comp βD.hom =
      ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation (IsLocalRing.closedPoint R) ≫ χR).hom := by
    change (ψD.comp δ.hom).comp ((algebraMap t.B A).comp t.α.hom) = _
    have hχhom :
        ((ΓSpecIso A).inv ≫ (Spec A).Γevaluation (IsLocalRing.closedPoint A) ≫ χA).hom.comp
          (algebraMap t.B A) =
        ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom :=
      congrArg CommRingCat.Hom.hom hχA
    rw [hψδ, ← RingHom.comp_assoc, hχhom]
    exact congrArg CommRingCat.Hom.hom t.compatible
  obtain ⟨g, hg, hug⟩ := pointed_colimit_lift R _ K χR c hc ρ hρ ψ hψ
    d.pt βD ψD hsD hkD hredD
  have hstage : g.comp (c.ι.app t).hom = δ.hom.comp (algebraMap t.B A) := by
    obtain ⟨l, hl, hul⟩ := etale_henselian_ring_lift R t.B d.pt t.α t.etale βD K
      ψD hsD hkD (((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ).hom)
      (by exact (congrArg CommRingCat.Hom.hom t.compatible).trans hredD.symm)
    apply (hul _ ?_).trans (hul _ ?_).symm
    · constructor
      · rw [RingHom.comp_assoc, ← CommRingCat.hom_comp, hρ t, hg.1]
      · rw [← RingHom.comp_assoc, hg.2, hψ t]
    · constructor
      · rfl
      · rw [← RingHom.comp_assoc, hψδ]
        exact congrArg CommRingCat.Hom.hom hχA
  have hbaseG : g.comp βC = δ.hom := by
    apply IsLocalization.ringHom_ext t.q.asIdeal.primeCompl
    rw [RingHom.comp_assoc, hβC, hstage]
  have hfg : f.comp g = RingHom.id c.pt := by
    obtain ⟨l, hl, hul⟩ := pointed_colimit_lift R _ K χR c hc ρ hρ ψ hψ
      c.pt ρ ψ hsC hkC hψρ
    apply (hul _ ?_).trans (hul _ ?_).symm
    · constructor
      · rw [RingHom.comp_assoc, hg.1]
        change (f.comp δ.hom).comp ((algebraMap t.B A).comp t.α.hom) = ρ.hom
        rw [hf.1, ← RingHom.comp_assoc, hβC]
        exact congrArg CommRingCat.Hom.hom (hρ t)
      · rw [← RingHom.comp_assoc, hf.2, hg.2]
    · simp
  have hgf : g.comp f = RingHom.id d.pt := by
    obtain ⟨l, hl, hul⟩ := pointed_colimit_lift A _ K χA d hd δ hδ ψD hψD
      d.pt δ ψD hsD hkD hψδ
    apply (hul _ ?_).trans (hul _ ?_).symm
    · constructor
      · rw [RingHom.comp_assoc, hf.1, hbaseG]
      · rw [← RingHom.comp_assoc, hg.2, hf.2]
    · simp
  let e : d.pt ≃+* c.pt :=
    { f with
      invFun := g
      left_inv := fun x ↦ DFunLike.congr_fun hgf x
      right_inv := fun x ↦ DFunLike.congr_fun hfg x }
  refine ⟨e, ⟨?_, hf.2⟩, ?_⟩
  · change f.comp (δ.hom.comp (algebraMap t.B A)) = (c.ι.app t).hom
    rw [← RingHom.comp_assoc, hf.1, hβC]
  · intro e' he'
    have hbase : e'.toRingHom.comp δ.hom = βC := by
      apply IsLocalization.ringHom_ext t.q.asIdeal.primeCompl
      rw [RingHom.comp_assoc, he'.1, hβC]
    have heq := huf e'.toRingHom ⟨hbase, he'.2⟩
    exact RingEquiv.toRingHom_injective heq

end AlgebraicGeometry.Scheme
