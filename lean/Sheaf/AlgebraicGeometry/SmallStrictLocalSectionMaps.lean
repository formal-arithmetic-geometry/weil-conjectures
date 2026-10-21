/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization

/-! # Section maps in the small strict-henselization presentation

Source: Stacks Project, Tag 03Q9, degree zero for sets, with Tags 09YQ and 09YU
(blueprint: def-weil-pbc-small-strict-local-section-maps).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison of the small ring colimit with the full affine colimit is over the base.
Source: Stacks Project, Tag 03Q9, independence of the affine representative category.
(blueprint: def-weil-pbc-small-strict-local-section-maps). -/
theorem smallStrictLocalization_toBase
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


/-- The map X^sh → V ×_Y X with components c_V ∘ f^sh and p, for a representative affine
pointed neighbourhood `j`.
Source: Stacks Project, Tag 03Q9, fibre products commuting with limits
(blueprint: def-weil-pbc-small-strict-local-section-maps). -/
@[irreducible]
noncomputable def smallStrictHenselizationBaseChangeMap
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) :
    pullback (strictHenselizationStructuralMap y) f ⟶
      pullback ((AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom f :=
  pullback.map (strictHenselizationStructuralMap y) f (strictLocalizationToBase y) f
    (Spec.map (smallStrictHenselizationColimitIso y).inv) (𝟙 X) (𝟙 Y)
    (by simpa using (smallStrictLocalization_toBase y).symm) (by simp) ≫
      strictHenselizationBaseChangeMap f y j

/-- Projection of the transported leg to X.
Source: Stacks Project, Tag 03Q9, fibre product projections.
(blueprint: def-weil-pbc-small-strict-local-section-maps). -/
@[reassoc (attr := simp)]
theorem smallStrictHenselizationBaseChangeMap_snd
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) :
    smallStrictHenselizationBaseChangeMap f y j ≫ pullback.snd _ f =
      pullback.snd (strictHenselizationStructuralMap y) f := by
  simp [smallStrictHenselizationBaseChangeMap, strictHenselizationBaseChangeMap,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transported leg has the original small spectrum-cone projection.
Source: Stacks Project, Tag 03Q9, compatibility of the canonical colimit comparison.
(blueprint: def-weil-pbc-small-strict-local-section-maps). -/
@[reassoc]
theorem smallStrictHenselizationBaseChangeMap_fst
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) :
    smallStrictHenselizationBaseChangeMap f y j ≫ pullback.fst _ f =
      pullback.fst (strictHenselizationStructuralMap y) f ≫
        (strictHenselizationCone y).π.app (op (op j)) ≫
          Spec.map (ΓSpecIso
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj
              j).1.left.unop).inv := by
  let : HasColimit (strictHenselizationDiagram y) := inferInstance
  let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse
  let incl := strictHenselizationAffineInclusion y
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence y
  have hleg := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (strictHenselizationDiagram y) (op j)
  change colimit.ι (strictHenselizationDiagram y) (op (incl.obj (rep.obj j))) ≫
    (smallStrictHenselizationColimitIso y).inv =
      colimit.ι (strictHenselizationAffineDiagram y) (op j) at hleg
  simp only [smallStrictHenselizationBaseChangeMap, strictHenselizationBaseChangeMap,
    Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  change _ ≫ Spec.map (smallStrictHenselizationColimitIso y).inv ≫
    Spec.map (colimit.ι (strictHenselizationDiagram y) (op (incl.obj (rep.obj j)))) ≫ _ =
      _ ≫ Spec.map (colimit.ι (strictHenselizationAffineDiagram y) (op j)) ≫ _
  have hh := congrArg (fun z ↦ Spec.map z ≫ Spec.map (ΓSpecIso
    ((rep.obj j).1.left.unop)).inv) hleg
  simp only [Spec.map_comp, Category.assoc] at hh
  exact congrArg (fun z ↦ pullback.fst (strictHenselizationStructuralMap y) f ≫ z) hh

/-- The site morphism σ_V from the final object to the iterated fibre product.
Source: Stacks Project, Tag 03Q9, canonical section restriction
(blueprint: def-weil-pbc-small-strict-local-section-maps). -/
noncomputable def smallStrictHenselizationSectionMap
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) :
    Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤
        (pullback.snd (strictHenselizationStructuralMap y) f)).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (smallStrictHenselizationBaseChangeMap f y j) (𝟙 _)
      (smallStrictHenselizationBaseChangeMap_snd f y j)) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme

