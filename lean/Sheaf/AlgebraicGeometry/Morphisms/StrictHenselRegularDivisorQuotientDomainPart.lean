module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
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

/-- The divisor quotient of the canonical strict henselization is a domain.
Source: Stacks Project, Tag 00NP.
Proof: The local-structure theorem makes the canonical strict henselization local.
Since b(f) is not a unit, its principal ideal is proper, so the quotient is nontrivial
and local. The regularity component makes this quotient regular, hence regular local.
Apply the proved upstream theorem that a regular local ring is a domain.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-domain-part)
-/
theorem strictHenselizationRing_divisor_quotient_domain_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  obtain ⟨hlocal, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  let := hlocal
  let : IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
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
  have hproper : Ideal.span {b.hom f} ≠ ⊤ := fun h ↦
    hg (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let := IsRegularLocalRing.of_isRegularRing_of_isLocalRing
    (R := strictHenselizationRing barY ⧸ Ideal.span {b.hom f})
  infer_instance

end AlgebraicGeometry.Scheme
