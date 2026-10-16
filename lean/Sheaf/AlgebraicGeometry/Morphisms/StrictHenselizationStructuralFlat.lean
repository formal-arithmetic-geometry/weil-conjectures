/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Flatness of the canonical affine strict henselization map
Source: Stacks Project, Tags 04HX and 07QM; Tag 0EYG, first reduction paragraph.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ring map inducing the canonical strict henselization structural map is flat.
Source: Stacks Project, Tags 04HX and 07QM; Tag 0EYG, first reduction paragraph.
(blueprint: lem-sbc-affine-strict-henselization-structural-flat)

Proof: For an affine base Spec R, the pointed affine etale neighbourhood coordinate
rings are etale R-algebras. The canonical structural map restricts to their
structure maps, by its defining common-composite identity. Thus the canonical
colimit ring is the filtered colimit of flat R-modules (etale algebras are flat).
Filtered colimits of flat modules are flat. Spec is faithful on ring maps,
so the displayed structural-map equality identifies b with this canonical
colimit algebra map. This works at any geometric point, whether or not it lies
on a specified divisor; no regularity or Noetherian hypothesis is needed. -/
theorem strictHenselization_structural_ringHom_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom := by
  classical
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
  let J := (SmallModel.{u} (strictHenselizationNeighbourhoods barY))ᵒᵖ
  let D := smallStrictHenselizationDiagram barY
  let f (j : J) : Spec (N.obj j.unop).1.left.unop ⟶ Spec R :=
    ((AffineEtale.Spec (Spec R)).obj (N.obj j.unop).1).hom
  have : IsCofiltered (SmallModel.{u} (strictHenselizationNeighbourhoods barY)) :=
    (strictHenselization_properties barY).2.1
  let t : (Functor.const J).obj R ⟶ D :=
    { app := fun j ↦ (ΓSpecIso R).inv ≫ (f j).appTop
      naturality := by
        intro i j g
        have hw : Spec.map (N.map g.unop).1.left.unop ≫ f i = f j :=
          (N.map g.unop).1.w
        have h := congrArg Scheme.Hom.appTop hw
        rw [Scheme.Hom.comp_appTop] at h
        change (𝟙 R) ≫ ((ΓSpecIso R).inv ≫ (f j).appTop) =
          ((ΓSpecIso R).inv ≫ (f i).appTop) ≫
            (Spec.map (N.map g.unop).1.left.unop).appTop
        rw [Category.id_comp, Category.assoc]
        exact congrArg (fun k ↦ (ΓSpecIso R).inv ≫ k) h.symm }
  let c : D ⟶ (Functor.const J).obj (strictHenselizationRing barY) := by
    first
    | exact (colimit.cocone D).ι
    | exact (smallStrictHenselizationCocone barY).ι
  have hc : IsColimit (Cocone.mk (strictHenselizationRing barY) c) := by
    first
    | exact colimit.isColimit D
    | exact isColimitSmallStrictHenselizationCocone barY
  apply RingHom.Flat.of_isColimit b J D (t := t) hc
  intro j
  refine ⟨?_, ?_⟩
  · change (((f j).appTop).hom.comp (ΓSpecIso R).inv.hom).Flat
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv))
      ((f j).flat_appTop)
  · apply Spec.map_injective
    rw [hb]
    have h := strictHenselizationStructuralMap_eq barY j.unop
    change Spec.map (t.app j ≫ c.app j) = _
    rw [Spec.map_comp]
    change Spec.map (c.app j) ≫
      Spec.map ((ΓSpecIso R).inv ≫ (f j).appTop) = _
    have ht : (ΓSpecIso R).inv ≫ (f j).appTop =
        Spec.preimage (f j) ≫ (ΓSpecIso (N.obj j.unop).1.left.unop).inv := by
      simp [ΓSpecIso_inv_naturality]
    rw [ht, Spec.map_comp, Spec.map_preimage]
    exact h

end AlgebraicGeometry.Scheme
