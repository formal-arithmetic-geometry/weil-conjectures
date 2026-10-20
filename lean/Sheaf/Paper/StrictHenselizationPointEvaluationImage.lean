/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
import Sheaf.Paper.StrictHenselizationPointEvaluationPointed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Image of pointed evaluation

Source: Stacks Project, Tags 04GW and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Evaluation of a section at a field-valued point of an étale morphism is
separable over the base residue field. Source: Stacks Project, Tag 04GW.
Factor the point through its residue field, use étaleness of the induced residue-field
extension, then map the resulting separable element into Ω. -/
private theorem affine_eval_mem
    {X S : Scheme.{v}} {Ω : Type v} [Field Ω]
    (g : X ⟶ S) [Etale g] (s : Spec (.of Ω) ⟶ X)
    (b : Γ(X, ⊤))
    [Algebra (S.residueField (g (s (IsLocalRing.closedPoint Ω)))) Ω]
    (hbase : algebraMap (S.residueField (g (s (IsLocalRing.closedPoint Ω)))) Ω =
      (descResidueField (stalkClosedPointTo (s ≫ g))).hom) :
    (ΓSpecIso (.of Ω)).hom (s.appTop b) ∈
      separableClosure (S.residueField (g (s (IsLocalRing.closedPoint Ω)))) Ω := by
  let q := s (IsLocalRing.closedPoint Ω)
  let p := g q
  let F := S.residueField p
  let L := X.residueField q
  let m := g.residueFieldMap q
  let e := X.descResidueField (stalkClosedPointTo s)
  let : Algebra F L := m.hom.toAlgebra
  have hm : m.hom.Etale := g.etale_residueFieldMap q
  let : Algebra.Etale F L := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hm
  have hsep : Algebra.IsSeparable F L :=
    (Algebra.FormallyEtale.iff_isSeparable F L).mp inferInstance
  have hcomp : m ≫ e = descResidueField (stalkClosedPointTo (s ≫ g)) := by
    rw [descResidueField_stalkClosedPointTo_comp]
  have hbase' : algebraMap F Ω =
      (descResidueField (stalkClosedPointTo (s ≫ g))).hom := by
    simpa [F, p, q] using hbase
  let a : L →ₐ[F] Ω :=
    { e.hom with
      commutes' r := by
        have hh : CommRingCat.ofHom (algebraMap F L) ≫ e =
            CommRingCat.ofHom (algebraMap F Ω) := by
          have hbcat : CommRingCat.ofHom (algebraMap F Ω) =
              descResidueField (stalkClosedPointTo (s ≫ g)) := by
            exact congrArg CommRingCat.ofHom hbase'
          rw [hbcat]
          change CommRingCat.ofHom (algebraMap F L) ≫ e =
            descResidueField (stalkClosedPointTo (s ≫ g))
          change m ≫ e = descResidueField (stalkClosedPointTo (s ≫ g))
          exact hcomp
        exact congrArg (fun f => f.hom r) hh }
  let z := (X.fromSpecResidueField q).appTop b
  let w := (ΓSpecIso L).hom z
  have hz : IsSeparable F (a w) :=
    (Algebra.IsSeparable.isSeparable F w).map a a.injective
  have hzmem : a w ∈ separableClosure F Ω := mem_separableClosure_iff.mpr hz
  have heval : (ΓSpecIso (.of Ω)).hom (s.appTop b) = a w := by
    have hf := descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X s
    rw [← hf, Hom.comp_appTop]
    exact congrArg (fun t ↦ t ((X.fromSpecResidueField q).appTop b))
      (ΓSpecIso_naturality e)
  rw [heval]
  exact hzmem

/-- Pointed evaluation lands in the relative separable closure.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
Source: Stacks Project, Tag 04HX. Represent a colimit element by an affine pointed
étale neighbourhood; its residue extension is finite separable over the base residue
field, so its chosen embedding into Ω lands in the relative separable closure. -/
theorem strictHenselizationPointEvaluation_mem
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom)
    (a : strictHenselizationRing barY) :
    strictHenselizationPointEvaluation barY a ∈
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω := by
  classical
  let C := SmallModel (strictHenselizationNeighbourhoods barY)
  let : IsCofiltered C := (strictHenselization_properties barY).2.1
  let : IsFiltered Cᵒᵖ := inferInstance
  let : FinallySmall Cᵒᵖ := finallySmall_of_essentiallySmall Cᵒᵖ
  let : PreservesColimitsOfShape Cᵒᵖ (CategoryTheory.forget CommRingCat) := by
    apply FinallySmall.preservesColimitsOfShape_of_isFiltered
  obtain ⟨j, b, hb⟩ := Concrete.isColimit_exists_rep
    (strictHenselizationAffineDiagram barY)
    (colimit.isColimit (strictHenselizationAffineDiagram barY)) a
  rw [← hb]
  let M := (equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj j.unop
  let X := Spec M.1.left.unop
  have he := strictHenselizationPointEvaluation_pointed barY j.unop
  have hs : Spec.map (M.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom) ≫ X.isoSpec.inv =
      M.2.left := by
    rw [Spec.map_comp, AlgebraicGeometry.SpecMap_ΓSpecIso_hom,
      ← toSpecΓ_naturality]
    change (M.2.left ≫ X.toSpecΓ) ≫ X.isoSpec.inv = M.2.left
    rw [Category.assoc, toSpecΓ_isoSpec_inv X]
    exact Category.comp_id M.2.left
  have heq : (colimit.ι (strictHenselizationAffineDiagram barY) j) ≫
      CommRingCat.ofHom (strictHenselizationPointEvaluation barY) =
      M.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom := by
    apply Spec.map_injective
    apply (cancel_mono X.isoSpec.inv).mp
    rw [Spec.map_comp]
    exact he.trans hs.symm
  have hev := congrArg (fun f => f.hom b) heq
  change strictHenselizationPointEvaluation barY
      (((colimit.cocone (strictHenselizationAffineDiagram barY)).ι.app j).hom b) = _ at hev
  rw [hev]
  have hM : M.2.left ≫ M.1.hom = barY := Over.w M.2
  let q := M.2.left (IsLocalRing.closedPoint Ω)
  have hq : M.1.hom q = barY (IsLocalRing.closedPoint Ω) :=
    congrArg (fun f : Spec (.of Ω) ⟶ Y ↦ f (IsLocalRing.closedPoint Ω)) hM
  let : Algebra (Y.residueField (M.1.hom q)) Ω :=
    ((algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω).comp
      (Y.residueFieldCongr hq).hom.hom).toAlgebra
  let : Etale M.1.hom := M.1.prop
  let G := Y.residueField (barY (IsLocalRing.closedPoint Ω))
  let emb := (SpecToEquivOfField Ω X M.2.left).2
  have hemb : emb.hom.comp (M.1.hom.residueFieldMap q).hom =
      (algebraMap G Ω).comp (Y.residueFieldCongr hq).hom.hom := by
    obtain ⟨_, hh⟩ := SpecToEquivOfField_eq_iff.mp
      (congrArg (SpecToEquivOfField Ω Y) hM)
    dsimp [SpecToEquivOfField] at hh
    rw [descResidueField_stalkClosedPointTo_comp] at hh
    have hh' := congrArg (fun f ↦ (Y.residueFieldCongr hq).inv ≫ f) hh
    simp only [Iso.inv_hom_id_assoc] at hh'
    change emb.hom.comp (M.1.hom.residueFieldMap q).hom = _
    have hbcat : CommRingCat.ofHom (algebraMap G Ω) =
        descResidueField (stalkClosedPointTo barY) :=
      congrArg CommRingCat.ofHom hΩ
    rw [← hbcat] at hh'
    have hh'' := congrArg (fun f ↦ (Y.residueFieldCongr hq).hom ≫ f) hh'
    simp only [Iso.hom_inv_id_assoc] at hh''
    have hh''' := congrArg CommRingCat.Hom.hom hh''
    simpa [CommRingCat.hom_comp, emb, X, q, SpecToEquivOfField] using hh'''
  have hbase : algebraMap (Y.residueField (M.1.hom q)) Ω =
      (descResidueField (stalkClosedPointTo (M.2.left ≫ M.1.hom))).hom := by
    change (algebraMap G Ω).comp (Y.residueFieldCongr hq).hom.hom = _
    rw [descResidueField_stalkClosedPointTo_comp (f := M.1.hom)]
    exact hemb.symm
  have hm := affine_eval_mem (X := X) (S := Y) M.1.hom M.2.left b hbase
  have hs : IsSeparable (Y.residueField (M.1.hom q))
      ((ΓSpecIso (.of Ω)).hom (M.2.left.appTop b)) :=
    mem_separableClosure_iff.mp hm
  have hsg : IsSeparable G ((ΓSpecIso (.of Ω)).hom (M.2.left.appTop b)) :=
    hs.of_equiv_equiv (Y.residueFieldCongr hq).commRingCatIsoToRingEquiv
      (RingEquiv.refl Ω) (by rfl)
  rw [mem_separableClosure_iff]
  exact hsg

end AlgebraicGeometry.Scheme
