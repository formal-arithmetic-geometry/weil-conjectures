/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitBaseMapNaturality
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Auxiliary limit statements for punctured root charts
Source: Stacks Project, Tags 0BSK, 05N9 and 01YW. -/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The categorical calculations below need a larger heartbeat budget than the default.
/-- The pointed etale neighbourhoods give a ring-colimit presentation over the base.

Source: Stacks Project, Tag 0BSK; canonical structural map, Tag 03Q9.
(blueprint: lem-sbc-pointed-etale-ring-colimit)

Proof: Take the small representative category of affine pointed etale neighbourhoods.
Its opposite-indexed global-section diagram is strictHenselizationAffineDiagram barY, and its
canonical colimit is strictHenselizationRing barY. Cofilteredness follows from
strictHenselization_properties. The structure maps from R are obtained by applying global
sections to the neighbourhood structure morphisms and using GammaSpecIso. Their naturality
follows from the over-category equations. The colimit legs composed with these maps equal b:
apply Spec, use strictHenselizationStructuralMap_eq and hb, and use faithfulness of Spec.
Each neighbourhood is etale by its AffineEtale structure. Its lift of barY supplies a point
above y: choose the zero prime of the field Omega, map it by the lift, and apply hy to the
over-category equality. Transfer these points through the affine-spectrum isomorphisms. -/
theorem pointed_etale_ring_colimit
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c : Cocone F)
        (a : (Functor.const Iᵒᵖ).obj R ⟶ F)
        (e : c.pt ≅ strictHenselizationRing barY),
        Nonempty (IsColimit c) ∧
        (∀ j, a.app j ≫ c.ι.app j ≫ e.hom = b) ∧
        ∀ j, Etale (Spec.map (a.app j)) ∧
          ∃ z : Spec (F.obj j), (Spec.map (a.app j)) z = y := by
  let I := SmallModel.{u} (strictHenselizationNeighbourhoods barY)
  let F := strictHenselizationAffineDiagram barY
  let c := colimit.cocone F
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
  let a : (Functor.const Iᵒᵖ).obj R ⟶ F :=
    { app := fun j => (ΓSpecIso R).inv ≫ Scheme.Γ.map (N.obj j.unop).1.hom.op
      naturality := by
        intro j k f
        simp only [Functor.const_obj_map]
        exact strictHenselization_baseRingMap_naturality R barY f }
  refine ⟨I, inferInstance, ?_⟩
  let hcof : IsCofiltered I := (strictHenselization_properties barY).2.1
  let e : c.pt ≅ strictHenselizationRing barY := by
    dsimp [c, F, strictHenselizationRing]
    exact Iso.refl _
  refine ⟨hcof, F, c, a, e, ?_, ?_, ?_⟩
  · exact ⟨colimit.isColimit F⟩
  · intro j
    dsimp [a, F, N]
    apply AlgebraicGeometry.Spec.map_injective
    simp only [AlgebraicGeometry.Spec.map_comp, Category.assoc]
    have hleg : Spec.map e.hom ≫ Spec.map (c.ι.app j) =
        (strictHenselizationCone barY).π.app (Opposite.op j) := by
      dsimp [F, e, c, strictHenselizationCone]
      rw [AlgebraicGeometry.Spec.map_id]
      exact Category.id_comp (Spec.map (colimit.ι
        (strictHenselizationAffineDiagram barY) j))
    rw [← Category.assoc, hleg]
    rw [← AlgebraicGeometry.Spec.map_comp]
    let V := Scheme.Spec.obj
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
        j.unop).1.left
    let g := ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
      j.unop).1.hom
    have hg : V.toSpecΓ ≫ Spec.map ((ΓSpecIso R).inv ≫ g.appTop) = g := by
      rw [Spec.map_comp, ← toSpecΓ_naturality_assoc]
      change g ≫ (Spec R).toSpecΓ ≫ Spec.map (ΓSpecIso R).inv = g
      rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
      exact Category.comp_id _
    have heq : Spec.map ((ΓSpecIso R).inv ≫ g.appTop) = V.isoSpec.inv ≫ g := by
      rw [← hg, ← Category.assoc]
      simp [V, Scheme.isoSpec]
    rw [heq]
    have hV : V.isoSpec.inv ≫ g =
        Spec.map (ΓSpecIso
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
            j.unop).1.left.unop).inv ≫
          ((AffineEtale.Spec (Spec R)).obj
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
              j.unop).1).hom := by
      dsimp [V, g]
      simp [Scheme.isoSpec, AffineEtale.Spec_obj_hom]
    rw [hV]
    rw [strictHenselizationStructuralMap_eq barY j.unop, ← hb]
  · intro j
    dsimp [a, F, N]
    let V := Scheme.Spec.obj
      ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
        j.unop).1.left
    let g := ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
      j.unop).1.hom
    have hg : V.toSpecΓ ≫ Spec.map ((ΓSpecIso R).inv ≫ g.appTop) = g := by
      rw [Spec.map_comp, ← toSpecΓ_naturality_assoc]
      change g ≫ (Spec R).toSpecΓ ≫ Spec.map (ΓSpecIso R).inv = g
      rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
      exact Category.comp_id _
    have heq : Spec.map ((ΓSpecIso R).inv ≫ g.appTop) = V.isoSpec.inv ≫ g := by
      rw [← hg, ← Category.assoc]
      simp [V, Scheme.isoSpec]
    have hV : V.isoSpec.inv ≫ g =
        Spec.map (ΓSpecIso
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
            j.unop).1.left.unop).inv ≫
          ((AffineEtale.Spec (Spec R)).obj
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
              j.unop).1).hom := by
      dsimp [V, g]
      simp [Scheme.isoSpec, AffineEtale.Spec_obj_hom]
    constructor
    · rw [heq]
      rw [hV]
      infer_instance
    · let v :=
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
          j.unop).2.left
      let z : Spec (F.obj j) := (v ≫ V.toSpecΓ) (IsLocalRing.closedPoint Ω)
      have hv : v ≫ g = barY := by
        simpa [v, g] using
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse.obj
            j.unop).2.w
      have hscheme : v ≫ V.toSpecΓ ≫
          Spec.map ((ΓSpecIso R).inv ≫ g.appTop) = barY := by
        calc
          v ≫ V.toSpecΓ ≫ Spec.map ((ΓSpecIso R).inv ≫ g.appTop) = v ≫ g := by
            rw [hg]
          _ = barY := hv
      refine ⟨z, ?_⟩
      have hp := congrArg (fun q : Spec (.of Ω) ⟶ Spec R =>
        q (IsLocalRing.closedPoint Ω)) hscheme
      have hp' : Spec.map ((ΓSpecIso R).inv ≫ g.appTop) z =
          barY (IsLocalRing.closedPoint Ω) := by
        change (Spec.map ((ΓSpecIso R).inv ≫ g.appTop))
            ((v ≫ V.toSpecΓ) (IsLocalRing.closedPoint Ω)) = _
        exact hp
      exact hp'.trans (hy _)

end AlgebraicGeometry.Scheme
