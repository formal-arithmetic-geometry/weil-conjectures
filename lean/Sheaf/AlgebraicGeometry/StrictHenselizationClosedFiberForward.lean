module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

open Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem small_toBase
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (smallStrictHenselizationColimitIso s).inv ≫ strictLocalizationToBase s =
      strictHenselizationStructuralMap s := by
  classical
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let incl := strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
  have := (strictHenselization_properties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  have hbig := strictLocalizationCone_π_app_hom s (incl.obj (rep.obj j))
  rw [strictLocalizationCone_π_app] at hbig
  have hsmall := (exists_strictHenselizationStructuralMap s).choose_spec j
  have hleg := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (strictHenselizationDiagram s) (op j)
  change colimit.ι (strictHenselizationDiagram s) (op (incl.obj (rep.obj j))) ≫
    (smallStrictHenselizationColimitIso s).inv =
      colimit.ι (strictHenselizationAffineDiagram s) (op j) at hleg
  let B := (rep.obj j).1.left.unop
  let f : Spec B ⟶ S := ((AffineEtale.Spec S).obj (rep.obj j).1).hom
  change (Spec.map (colimit.ι (strictHenselizationDiagram s)
      (op (incl.obj (rep.obj j)))) ≫ inv (Spec B).toSpecΓ) ≫ f =
    strictLocalizationToBase s at hbig
  change Spec.map (colimit.ι (strictHenselizationAffineDiagram s) (op j)) ≫
    Spec.map (ΓSpecIso B).inv ≫ f = strictHenselizationStructuralMap s at hsmall
  have hinv : inv (Spec B).toSpecΓ = Spec.map (ΓSpecIso B).inv := by
    apply (cancel_mono (Spec B).toSpecΓ).1
    simp only [IsIso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]
  rw [hinv] at hbig
  have hh := congrArg (fun z ↦ Spec.map z ≫ Spec.map (ΓSpecIso B).inv ≫ f) hleg
  simp only [Spec.map_comp, Category.assoc] at hh
  rw [← hbig]
  simpa only [Category.assoc] using hh.trans hsmall

set_option autoImplicit false
/-- The strict henselization structural fibre over the distinguished point contains no
point other than the closed point. This is the forward half of the singleton-fibre theorem.
Source: Stacks Project, Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber-forward)
Proof: choose an affine chart Spec R around p = s(closedPoint Ω) and factor s
through it. The initial chart restriction and the pointed etale residue-triple equivalence
identify the coordinate-ring colimit C defining the strict henselization with the triple
colimit, preserving the structural R-map on every coprojection. The residue embeddings
land in the relative separable closure of κ(p) inside Ω since etale residue extensions
are finite separable (Tag 04HX). Tags 04GW and 04GP give a local colimit whose maximal
ideal is pC. The prime corresponding to e(x) contracts to p, so it contains pC and equals
that maximal ideal. Therefore e(x) is the closed point of Spec C. An isomorphism preserves
closed singletons; its inverse sends this point to the unique closed point of Spec A.
Thus x = closedPoint A. The argument includes the field case. A zero ring A cannot have
the assumed isomorphism, since C has a nonzero field quotient. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictHenselizationStructuralMap s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A := by
  classical
  obtain ⟨R, i, hi, hp, _⟩ := exists_affine_mem_range_and_range_subset
    (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hrange : Set.range s ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hp
  let xR := IsOpenImmersion.lift i s hrange
  have hfac : xR ≫ i = s := IsOpenImmersion.lift_fac i s hrange
  have hchart := strictHenselization_chart_maximalIdeal R i xR
  rw [hfac] at hchart
  obtain ⟨hlocal, ρ₀, hρ₀, hm₀⟩ := hchart
  let := hlocal
  let eC : strictHenselizationRing s ≅ strictHenselization s :=
    smallStrictHenselizationColimitIso s
  let := eC.symm.commRingCatIsoToRingEquiv.isLocalRing
  let ρ := ρ₀ ≫ eC.inv
  have hρ : Spec.map ρ ≫ i = strictHenselizationStructuralMap s := by
    rw [Spec.map_comp, Category.assoc, hρ₀]
    exact small_toBase s
  have hm : IsLocalRing.maximalIdeal (strictHenselizationRing s) =
      (xR (IsLocalRing.closedPoint Ω)).asIdeal.map ρ.hom := by
    have h := IsLocalRing.map_ringEquiv_maximalIdeal eC.symm.commRingCatIsoToRingEquiv
    change (IsLocalRing.maximalIdeal (strictHenselization s)).map eC.inv.hom =
      IsLocalRing.maximalIdeal (strictHenselizationRing s) at h
    rw [← h, hm₀, Ideal.map_map]
    rfl
  have hcontract : Spec.map ρ (e.hom x) = xR (IsLocalRing.closedPoint Ω) := by
    apply i.isOpenEmbedding.injective
    have hh : (Spec.map ρ ≫ i) (e.hom x) = (xR ≫ i) (IsLocalRing.closedPoint Ω) := by
      rw [hρ, hfac]
      exact h
    simpa only [Scheme.Hom.comp_apply] using hh
  have hprime : (e.hom x).asIdeal =
      IsLocalRing.maximalIdeal (strictHenselizationRing s) := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (e.hom x).isPrime.ne_top
    · rw [hm, Ideal.map_le_iff_le_comap]
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal hcontract).symm
  have hx : e.hom x = IsLocalRing.closedPoint (strictHenselizationRing s) :=
    PrimeSpectrum.ext hprime
  have hspecial := (IsLocalRing.specializes_closedPoint
    (e.inv (IsLocalRing.closedPoint (strictHenselizationRing s))))
  have hback : IsLocalRing.closedPoint (strictHenselizationRing s) ⤳
      e.hom (IsLocalRing.closedPoint A) := by
    have ht := hspecial.map e.hom.continuous
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id] at ht
    exact ht
  have he : e.hom (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (strictHenselizationRing s) :=
    ((IsLocalRing.specializes_closedPoint _).antisymm hback).eq
  apply e.hom.isOpenEmbedding.injective
  exact hx.trans he.symm
end AlgebraicGeometry.Scheme
