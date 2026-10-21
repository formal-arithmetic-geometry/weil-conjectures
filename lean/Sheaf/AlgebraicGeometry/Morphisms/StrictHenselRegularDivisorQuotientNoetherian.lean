module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
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

/-- Noetherianity of the canonical strict henselization over a regular affine ring.
Source: Stacks Project, Tag 06LJ, applied to the local ring at the geometric point.
The proof identifies the coordinate-ring colimit with the ring strict henselization.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-noetherian)
-/
theorem strictHenselizationRing_noetherian_of_regular
    (R : CommRingCat.{u}) [IsRegularRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    IsNoetherianRing (strictHenselizationRing barY) := by
  let e : (R ⧸ Ideal.span ({0} : Set R)) ≃+* R := by
    rw [Ideal.span_singleton_zero]
    exact RingEquiv.quotientBot R
  letI : IsRegularRing (R ⧸ Ideal.span ({0} : Set R)) :=
    IsRegularRing.of_ringEquiv e.symm
  obtain ⟨hlocal, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  letI : IsLocalRing (strictHenselizationRing barY) := hlocal
  have hg : ¬ IsUnit (b.hom 0) := by
    intro hz
    have hz' : (0 : strictHenselizationRing barY) = 1 := by simpa using hz
    exact zero_ne_one hz'
  have h : IsRegularRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) := by
    let e : strictHenselizationRing barY ≅ strictHenselization barY :=
      smallStrictHenselizationColimitIso barY
    have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
      rw [Spec.map_comp, hb]
      exact comparison_base barY
    have hg' : ¬ IsUnit ((b ≫ e.hom).hom 0) := by
      intro h
      apply hg
      have h' := h.map e.inv.hom
      change IsUnit (e.commRingCatIsoToRingEquiv.symm
        (e.commRingCatIsoToRingEquiv (b.hom 0))) at h'
      simpa only [RingEquiv.symm_apply_apply] using h'
    have hQ := strictHenselizationRing_regular_divisor_quotient R 0 barY (b ≫ e.hom) hbe hg'
    let : IsRegularRing
        (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom 0}) := hQ.1
    let eQ : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom 0}) ≃+*
        (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) :=
      Ideal.quotientEquiv _ _ e.symm.commRingCatIsoToRingEquiv (by
        rw [Ideal.map_span, Set.image_singleton]
        change Ideal.span {b.hom 0} = Ideal.span {
          e.commRingCatIsoToRingEquiv.symm (e.commRingCatIsoToRingEquiv (b.hom 0))}
        rw [RingEquiv.symm_apply_apply])
    exact IsRegularRing.of_ringEquiv eQ
  letI : IsRegularRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) := h
  have hn : IsNoetherianRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) := inferInstance
  have ez : (strictHenselizationRing barY ⧸ Ideal.span {b.hom 0}) ≃+*
      strictHenselizationRing barY := by
    rw [show Ideal.span ({b.hom 0} : Set (strictHenselizationRing barY)) = ⊥ by
      simp]
    exact RingEquiv.quotientBot _
  exact isNoetherianRing_of_ringEquiv _ ez
end AlgebraicGeometry.Scheme
