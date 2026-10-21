module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart
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

/-- Regularity and integrality of the divisor quotient in the canonical strict henselization.
Source: Stacks Project, Tags 05WS and 06LN, using the local structure at the geometric point.
The quotient is identified with the strict henselization of the regular local divisor ring.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-regular)
-/
theorem strictHenselizationRing_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  have hregular : IsRegularRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
    let e : strictHenselizationRing barY ≅ strictHenselization barY :=
      smallStrictHenselizationColimitIso barY
    have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
      rw [Spec.map_comp, hb]
      exact comparison_base barY
    have hg' : ¬ IsUnit ((b ≫ e.hom).hom f) := by
      intro h
      apply hg
      have h' := h.map e.inv.hom
      change IsUnit (e.commRingCatIsoToRingEquiv.symm
        (e.commRingCatIsoToRingEquiv (b.hom f))) at h'
      simpa only [RingEquiv.symm_apply_apply] using h'
    let : IsRegularRing
        (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) :=
      strictHenselizationRing_regular_divisor_quotient_part R f barY (b ≫ e.hom) hbe hg'
    let eQ : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) ≃+*
        (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
      Ideal.quotientEquiv _ _ e.symm.commRingCatIsoToRingEquiv (by
        rw [Ideal.map_span, Set.image_singleton]
        change Ideal.span {b.hom f} = Ideal.span {
          e.commRingCatIsoToRingEquiv.symm (e.commRingCatIsoToRingEquiv (b.hom f))}
        rw [RingEquiv.symm_apply_apply])
    exact IsRegularRing.of_ringEquiv eQ
  exact ⟨hregular,
    strictHenselizationRing_divisor_quotient_domain_part R f barY b hb hg⟩
end AlgebraicGeometry.Scheme
