/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberForward

/-!
# Transport of the closed fibre to the small strict henselization

The canonical colimit isomorphism intertwines the small-model structural map with
`strictLocalizationToBase`. This transfers the upstream singleton-fibre theorem without
exposing its different structural-map compatibility API.

Source: Stacks Project, Tags 04GW, 04GP and 04HX.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.Scheme

open Limits Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Spec of the small-to-full colimit comparison commutes with the structure maps.
Source: Stacks Project, Tag 04HX, and the canonical final-functor colimit comparison.
(blueprint: lem-weil-pbc-strict-henselization-small-closed-fiber-comparison)

Proof: choose a representative pointed affine neighbourhood. The inverse colimit
comparison identifies its two coprojections. Apply Spec, identify the inverse of the
canonical affine global-sections map, and compose with the neighbourhood map to the base.
The defining equations of both structural maps identify the resulting composites. -/
theorem smallStrictHenselizationColimitIso_toBase
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (smallStrictHenselizationColimitIso s).inv ≫ strictLocalizationToBase s =
      strictHenselizationStructuralMap s := by
  classical
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let incl := strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
  have := (strictHenselization_properties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  have hbig := strictLocalizationCone_π_app_hom s (incl.obj (rep.obj j))
  rw [strictLocalizationCone_π_app] at hbig
  have hsmall := (exists_strictHenselizationStructuralMap s).choose_spec j
  have hleg := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (strictHenselizationDiagram s) (op j)
  change colimit.ι (strictHenselizationDiagram s) (op (incl.obj (rep.obj j))) ≫
    (smallStrictHenselizationColimitIso s).inv =
      colimit.ι (strictHenselizationAffineDiagram s) (op j) at hleg
  let B := (rep.obj j).1.left.unop
  let f : Spec B ⟶ S := ((AffineEtale.Spec S).obj (rep.obj j).1).hom
  change (Spec.map (colimit.ι (strictHenselizationDiagram s)
      (op (incl.obj (rep.obj j)))) ≫ inv (Spec B).toSpecΓ) ≫ f =
    strictLocalizationToBase s at hbig
  change Spec.map (colimit.ι (strictHenselizationAffineDiagram s) (op j)) ≫
    Spec.map (ΓSpecIso B).inv ≫ f = strictHenselizationStructuralMap s at hsmall
  have hinv : inv (Spec B).toSpecΓ = Spec.map (ΓSpecIso B).inv := by
    apply (cancel_mono (Spec B).toSpecΓ).1
    simp only [IsIso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]
  rw [hinv] at hbig
  have hh := congrArg (fun z ↦ Spec.map z ≫ Spec.map (ΓSpecIso B).inv ≫ f) hleg
  simp only [Spec.map_comp, Category.assoc] at hh
  rw [← hbig]
  simpa only [Category.assoc] using hh.trans hsmall

/-- The upstream closed-fibre theorem in the small-colimit presentation.
Source: Stacks Project, Tags 04GW, 04GP and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-small-closed-fiber-comparison)

Proof: the inverse of the canonical small-to-full colimit isomorphism has the same
coprojections as the small colimit. Applying Spec and composing one pointed-neighbourhood
leg with its structure map identifies the two structural maps. Compose the given affine
presentation with Spec of that inverse isomorphism and apply the upstream forward-fibre
theorem. The field case is included, and local-ring nontriviality excludes the zero ring. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_compat
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictHenselizationStructuralMap s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A := by
  let e' : Spec (.of A) ≅ strictLocalization s :=
    e ≪≫ asIso (Spec.map (smallStrictHenselizationColimitIso s).inv)
  apply strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq s e' x
  change ((e.hom ≫ Spec.map (smallStrictHenselizationColimitIso s).inv) ≫
    strictLocalizationToBase s) x = _
  simpa only [Category.assoc, smallStrictHenselizationColimitIso_toBase] using h

end AlgebraicGeometry.Scheme
