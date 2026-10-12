/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Image of pointed evaluation

Source: Stacks Project, Tags 04GW and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

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
  have := (strictHenselization_properties barY).2.1
  obtain ⟨j, b, rfl⟩ := Concrete.colimit_exists_rep (strictHenselizationDiagram barY) a
  let n := (equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj j.unop
  let V := Spec (unop n.1.left)
  let z : Spec (.of Ω) ⟶ V := n.2.left
  let g : V ⟶ Y := n.1.hom
  have hfac : z ≫ g = barY := Over.w n.2
  have heval : V.Γevaluation (z (IsLocalRing.closedPoint Ω)) ≫
      descResidueField (stalkClosedPointTo z) = z.appTop ≫ (ΓSpecIso (.of Ω)).hom := by
    dsimp [Γevaluation, evaluation]
    rw [Category.assoc, residue_descResidueField]
    simpa using germ_stalkClosedPointTo z ⊤ trivial
  have hc : strictHenselizationPointEvaluation barY
      (colimit.ι (strictHenselizationDiagram barY) j b) =
      (z.appTop ≫ (ΓSpecIso (.of Ω)).hom) b := by
    exact ConcreteCategory.congr_hom (colimit.ι_desc (strictHenselizationPointCocone barY) j) b
  rw [hc, ← heval]
  let F := Y.residueField (g (z (IsLocalRing.closedPoint Ω)))
  let L := V.residueField (z (IsLocalRing.closedPoint Ω))
  let f := g.residueFieldMap (z (IsLocalRing.closedPoint Ω))
  let e := descResidueField (stalkClosedPointTo z)
  let : Algebra F L := f.hom.toAlgebra
  let : Algebra F Ω := (f ≫ e).hom.toAlgebra
  have : Etale g := n.1.prop
  have : Algebra.IsSeparable F L := inferInstance
  let emb : L →ₐ[F] Ω := { e.hom with commutes' := fun _ ↦ rfl }
  have hsep := (Algebra.IsSeparable.isSeparable F (V.Γevaluation _ b)).map emb emb.injective
  apply mem_separableClosure_iff.mpr
  obtain ⟨hp, hh⟩ := SpecToEquivOfField_eq_iff.mp
    (congrArg (SpecToEquivOfField Ω Y) hfac)
  dsimp [SpecToEquivOfField] at hp hh
  rw [descResidueField_stalkClosedPointTo_comp] at hh
  let eqv := (Y.residueFieldCongr hp).commRingCatIsoToRingEquiv
  have hmaps : (algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω).comp
      eqv.toRingHom = algebraMap F Ω := by
    change (algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω).comp
      (Y.residueFieldCongr hp).hom.hom = (f ≫ e).hom
    rw [hΩ]
    exact congrArg CommRingCat.Hom.hom hh.symm
  exact hsep.of_equiv_equiv eqv (RingEquiv.refl Ω) hmaps

end AlgebraicGeometry.Scheme
