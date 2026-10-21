/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular

/-! # The regular divisor quotient of the canonical strict henselization
Source: Stacks Project, Tag 0EYG, strict henselization paragraph; Tags 06LN and 05WS.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The canonical colimit comparison identifies the structural maps.
Source: Stacks Project, Tag 04HX, via the final-functor coprojection formula. -/
private theorem comparison_base
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (smallStrictHenselizationColimitIso s).hom ≫
      strictHenselizationStructuralMap s = strictLocalizationToBase s := by
  classical
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let := (strictHenselization_properties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  have hs : (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
      Spec.map (ΓSpecIso
        (((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
      ((AffineEtale.Spec S).obj
        (((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
      strictHenselizationStructuralMap s :=
    (exists_strictHenselizationStructuralMap s).choose_spec j
  rw [← hs]
  have hι : colimit.ι (strictHenselizationAffineDiagram s) (Opposite.op j) ≫
      (smallStrictHenselizationColimitIso s).hom =
      (smallStrictHenselizationCocone s).ι.app (Opposite.op j) := by
    let := strictHenselizationAffineInclusion_isEquivalence s
    exact Functor.Final.ι_colimitIso_hom
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
        strictHenselizationAffineInclusion s).op (strictHenselizationDiagram s) (Opposite.op j)
  have hleg : Spec.map (smallStrictHenselizationColimitIso s).hom ≫
      (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) =
      (strictHenselizationAffineCone s).π.app (Opposite.op (Opposite.op j)) := by
    change Spec.map (smallStrictHenselizationColimitIso s).hom ≫
      Spec.map (colimit.ι (strictHenselizationAffineDiagram s) (Opposite.op j)) = _
    rw [← Spec.map_comp, hι]
    rfl
  rw [← Category.assoc, hleg]
  exact strictHenselizationStructuralMap_eq s j


/-- The canonical strict henselization is Noetherian and its nonempty divisor quotient
is a regular domain.
Source: Stacks Project, Tag 0EYG, strict henselization paragraph, using quotient
compatibility (Tag 05WS) and regularity of strict henselizations (Tag 06LN).
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient)

Proof: Let y be the image of the unique point of Spec Omega. The affine pointed
neighbourhood colimit identifies with the strict henselization of R localized at y.
That local ring is Noetherian and regular because R is regular. Strict henselization
preserves Noetherianness. The identity on Spec forces b to be its canonical map.
The nonunit condition says y is on the divisor. Quotient compatibility identifies
H/(b(f)) with the strict henselization of (R/(f)) localized at y. This is regular
local since R/(f) is regular. A regular local ring is a domain, and all its prime
localizations are regular local, so it is a regular ring. The nonunit condition
excludes the zero quotient; no choice of an arbitrary ring witness is made. -/
theorem strictHenselization_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY) ∧
      IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    smallStrictHenselizationColimitIso barY
  have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb]
    exact comparison_base barY
  let : IsNoetherianRing (strictHenselization barY) :=
    strictHenselizationRing_noetherian_of_regular R barY (b ≫ e.hom) hbe
  have hN : IsNoetherianRing (strictHenselizationRing barY) :=
    isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv
  have hQ :
      IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
        IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
    have hg' : ¬ IsUnit ((b ≫ e.hom).hom f) := by
      intro h
      apply hg
      have h' := h.map e.inv.hom
      change IsUnit (e.commRingCatIsoToRingEquiv.symm
        (e.commRingCatIsoToRingEquiv (b.hom f))) at h'
      simpa only [RingEquiv.symm_apply_apply] using h'
    have hQ := strictHenselizationRing_regular_divisor_quotient R f barY (b ≫ e.hom) hbe hg'
    let : IsRegularRing
        (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) := hQ.1
    let eQ : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) ≃+*
        (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
      Ideal.quotientEquiv _ _ e.symm.commRingCatIsoToRingEquiv (by
        rw [Ideal.map_span, Set.image_singleton]
        change Ideal.span {b.hom f} = Ideal.span {
          e.commRingCatIsoToRingEquiv.symm (e.commRingCatIsoToRingEquiv (b.hom f))}
        rw [RingEquiv.symm_apply_apply])
    refine ⟨IsRegularRing.of_ringEquiv eQ, eQ.toMulEquiv.isDomain_iff.mp ?_⟩
    exact hQ.2
  exact ⟨hN, hQ.1, hQ.2⟩

end AlgebraicGeometry.Scheme
