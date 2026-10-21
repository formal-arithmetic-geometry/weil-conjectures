module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.RegularLocalLocalization

/-! Local regularity and Noetherianity of the strict henselization divisor quotient. -/

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

/-- The divisor quotient has the local regularity properties needed to assemble a regular ring.
Source: Stacks Project, Tags 05WS and 06LN.
The presentation theorem identifies the quotient as an algebraic strict henselization of
a prime localization of `R/(f)`, without using regularity. The localization is regular
local by the assumed regularity of `R/(f)`. Apply the strict-henselization regularity
equivalence to deduce regular locality of the quotient, hence its Noetherianity. Finally
apply regular-local localization at every prime of the quotient.
(blueprint: lem-sbc-strict-hensel-regular-divisor-quotient-regular-part-aux)
-/
theorem strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      ∀ (p : Ideal (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}))
        [p.IsPrime],
    IsRegularLocalRing (Localization.AtPrime p) := by
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
  obtain ⟨p, hp, K, hK, aK, hsep, aLK, hLK, aLH, hH⟩ :=
    strictHenselizationRing_divisor_quotient_presentation R f barY (b ≫ e.hom) hbe hg'
  let := hp
  let := hK
  let := aK
  let := hsep
  let := aLK
  let := hLK
  let := aLH
  let eQ : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) ≃+*
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    Ideal.quotientEquiv _ _ e.symm.commRingCatIsoToRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {b.hom f} = Ideal.span {
        e.commRingCatIsoToRingEquiv.symm (e.commRingCatIsoToRingEquiv (b.hom f))}
      rw [RingEquiv.symm_apply_apply])
  let a : Algebra (Localization.AtPrime p)
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    (eQ.toRingHom.comp (algebraMap (Localization.AtPrime p)
      (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}))).toAlgebra
  let eAlg : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) ≃ₐ[
      Localization.AtPrime p] (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    { toRingEquiv := eQ
      commutes' _ := rfl }
  have hSmall : Algebra.IsStrictHenselization (Localization.AtPrime p) K
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
    obtain ⟨c, hc, ⟨i⟩⟩ := hH
    exact ⟨c, hc, ⟨i ≪≫ CommAlgCat.isoMk eAlg⟩⟩
  have hregL : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  have hregH : IsRegularLocalRing
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    (Algebra.isRegularLocalRing_iff_strictHenselization
      (Localization.AtPrime p) K _ hSmall).mp hregL
  let := hregH
  refine ⟨inferInstance, fun q hq ↦ ?_⟩
  exact (IsRegularLocalRing.localization_at_prime_and_isRegularRing q).1

end AlgebraicGeometry.Scheme
