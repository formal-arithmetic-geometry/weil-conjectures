/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation

/-!
# Local presentation for the small strict-henselization colimit

Transport the upstream presentation through the canonical comparison of affine colimits.
Source: Stacks Project, Tag 04HX.
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

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

/-- The small coordinate-ring colimit has the local presentation of the upstream affine
colimit, with its specified structural ring map preserved.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring).
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)

Proof: Compare the small representative colimit H with the affine-neighbourhood colimit
H' by their canonical colimit isomorphism e. The coprojection formula for e identifies
its spectrum with the two structural maps on any representative pointed neighbourhood.
Thus b followed by e has the structural-map equation required by the upstream local
presentation theorem. Retain its prime, separable closure and scalar tower. Pull the
local-base algebra structure back along e inverse. This makes e inverse an algebra
isomorphism, so composing it with the universal pointed-etale cocone isomorphism proves
IsStrictHenselization for H. The elementwise base-map equation follows by applying e
inverse to the equation for H'. No local algebra or ring is selected from mere existence.
-/
theorem smallStrictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing barY) := by
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    smallStrictHenselizationColimitIso barY
  have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb]
    exact comparison_base barY
  obtain ⟨q, hq, K, hK, ares, hsep, aK, htower, aH, hbase, hH⟩ :=
    strictHenselizationRing_local_presentation R barY (b ≫ e.hom) hbe
  let := hq
  let := hK
  let := ares
  let := hsep
  let := aK
  let := htower
  let := aH
  let a : Algebra (Localization.AtPrime q) (strictHenselizationRing barY) :=
    (e.inv.hom.comp (algebraMap (Localization.AtPrime q) (strictHenselization barY))).toAlgebra
  let f : strictHenselization barY ≃ₐ[Localization.AtPrime q] strictHenselizationRing barY :=
    { toRingEquiv := e.symm.commRingCatIsoToRingEquiv
      commutes' _ := rfl }
  refine ⟨q, hq, K, hK, ares, hsep, aK, htower, a, ?_, ?_⟩
  · intro r
    change e.inv.hom (algebraMap (Localization.AtPrime q) (strictHenselization barY)
      (algebraMap R (Localization.AtPrime q) r)) = b.hom r
    rw [hbase r]
    exact e.commRingCatIsoToRingEquiv.symm_apply_apply (b.hom r)
  · obtain ⟨c, hc, ⟨i⟩⟩ := hH
    exact ⟨c, hc, ⟨i ≪≫ CommAlgCat.isoMk f⟩⟩

end AlgebraicGeometry.Scheme
