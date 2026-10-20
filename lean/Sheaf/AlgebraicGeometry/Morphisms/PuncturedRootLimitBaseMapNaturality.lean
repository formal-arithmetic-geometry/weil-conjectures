/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-! # Naturality of affine pointed neighbourhood base maps
Source: Stacks Project, Tag 0BSK, proof of the pointed étale colimit presentation.
(blueprint: lem-sbc-pointed-etale-ring-colimit-base-map-naturality) -/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The maps from the affine base ring to the coordinate rings of representative pointed
étale neighbourhoods form a natural transformation. This is the global-sections form of
commutativity of the over-category triangles: for a morphism of representative pointed
neighbourhoods, the structure morphisms to `Spec R` commute, and contravariance of global
sections reverses that equality. Apply `Scheme.Hom.appTop` to the equality carried by
the over-category morphism, rewrite `Scheme.Hom.comp_appTop`, and precompose by
`(ΓSpecIso R).inv`.
Source: Stacks Project, Tag 0BSK, pointed étale colimit presentation.
(blueprint: lem-sbc-pointed-etale-ring-colimit-base-map-naturality) -/
theorem strictHenselization_baseRingMap_naturality
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    {j k : (SmallModel.{u} (strictHenselizationNeighbourhoods barY))ᵒᵖ}
    (f : j ⟶ k) :
    (ΓSpecIso R).inv ≫ Scheme.Γ.map
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
          k.unop).1.hom.op =
      ((ΓSpecIso R).inv ≫ Scheme.Γ.map
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
          j.unop).1.hom.op) ≫
        (strictHenselizationAffineDiagram barY).map f := by
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
  let q (i : (SmallModel.{u} (strictHenselizationNeighbourhoods barY))ᵒᵖ) :
      Scheme.Spec.obj (N.obj i.unop).1.left ⟶ Spec R :=
    ((AffineEtale.Spec (Spec R)).obj (N.obj i.unop).1).hom
  have hw : Spec.map (N.map f.unop).1.left.unop ≫ q j = q k :=
    (N.map f.unop).1.w
  have h := congrArg Scheme.Hom.appTop hw
  rw [Scheme.Hom.comp_appTop] at h
  change (ΓSpecIso R).inv ≫ (q k).appTop =
    ((ΓSpecIso R).inv ≫ (q j).appTop) ≫
      (Spec.map (N.map f.unop).1.left.unop).appTop
  rw [Category.assoc]
  exact congrArg (fun t ↦ (ΓSpecIso R).inv ≫ t) h.symm

end AlgebraicGeometry.Scheme
