/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Equality of exact and native direct-image compositors

Source: the native compositor comparison in the canonicity paragraph of the latest
blueprint's compact-support composition proof.
(blueprint: lem-sf-condensed-direct-compositor-normalization).

This isolates the already proved compositor calculation from
`CondensedTowerCompositorNormalization`, avoiding its compact-support composition data
and coefficient-specific dependencies.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CondensedOpenProper

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem exactAdjunction_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f) =
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction := by
  have hd : derivedUpperStarLowerStarAdjunction Λ f =
      ((upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (upperStar Λ f)).symm
  rw [hd]
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc]

private theorem conjugateTransport
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ L₁' L₂' : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (c : L₂' ≅ L₁') :
    conjugateIsoEquiv a₁ a₂ (e₂ ≪≫ c ≪≫ e₁.symm) =
      conjugateIsoEquiv (a₁.ofNatIsoLeft e₁) (a₂.ofNatIsoLeft e₂) c := by
  apply Iso.ext
  ext M
  simp [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Category.assoc]

private theorem compTransport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : D ⥤ E} {R₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') :
    (a₁.comp a₂).ofNatIsoLeft
        (Functor.isoWhiskerRight e₁ L₂ ≪≫ Functor.isoWhiskerLeft L₁' e₂) =
      (a₁.ofNatIsoLeft e₁).comp (a₂.ofNatIsoLeft e₂) := by
  apply Adjunction.ext
  ext M
  simp only [Adjunction.ofNatIsoLeft_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← R₁.map_comp_assoc]
  have hn := a₂.unit.naturality (e₁.hom.app M)
  change e₁.hom.app M ≫ a₂.unit.app (L₁'.obj M) =
    a₂.unit.app (L₁.obj M) ≫ R₂.map (L₂.map (e₁.hom.app M)) at hn
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]

/-- The direct-image compositor normalized by exact pullback agrees with the native total
left-derived compositor on every unbounded condensed-module derived category.

Source: the compositor comparison in the canonicity paragraph of
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-comp-composition/sk-thm-sf-comp-composition.proof.md`.
Proof: transport the native derived adjunction along the canonical exact-pullback
isomorphism. Uniqueness of derived adjunctions identifies it with the exact-left,
right-derived adjunction. Naturality of units shows that this transport commutes with
composition of adjunctions. Expand the native pullback compositor: it is the exact
pullback compositor conjugated by those same comparison isomorphisms. Conjugation
commutes with transport, so the right-adjoint compositors agree. The argument uses
only adjunction identities and applies also to identity maps and empty schemes.
(blueprint: lem-sf-condensed-direct-compositor-normalization). -/
theorem normalizedDirectCompositor_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedLowerStarComp Λ f g = rComp Λ f g := by
  let ef := leftDerivedUpperStarIsoMapDerivedCategory Λ f
  let eg := leftDerivedUpperStarIsoMapDerivedCategory Λ g
  let efg := leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)
  let ec := Functor.isoWhiskerRight eg ((upperStar Λ f).leftDerivedFunctor) ≪≫
    Functor.isoWhiskerLeft (P Λ g) ef
  have hc : leftDerivedUpperStarComp Λ f g =
      efg ≪≫ pComp Λ f g ≪≫ ec.symm := by
    apply Iso.ext
    ext M
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, ef, eg, efg, ec, pComp,
      leftDerivedUpperStarIsoMapDerivedCategory]
  unfold rightDerivedLowerStarComp
  rw [hc, conjugateTransport, compTransport, exactAdjunction_eq,
    exactAdjunction_eq, exactAdjunction_eq]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
