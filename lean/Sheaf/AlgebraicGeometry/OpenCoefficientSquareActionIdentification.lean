/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.ExtensionIsoQuotientFormula
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # The identity action normalization of the open coefficient square

Source: main-20261015 blueprint, sec-six-functors-basics,
sk-def-sfb-coefficient-comparisons/def-sfb-comap-upper-star-iso.proof.md and
 def-sfb-derived-comap-upper-star-iso.proof.md
(blueprint: lem-sfb-open-coefficient-square-action-identification).

The auxiliary constructions retain the specified balanced collapse and build the reverse
comparison from restriction along the inverse coefficient maps. No coefficient flatness is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X)

/-- Pullback written using restriction along the inverse coefficient isomorphism.
Source: def-sfb-comap-upper-star-iso.proof.md, inverse-coefficient identification
(blueprint: lem-sfb-open-coefficient-square-action-identification). -/
noncomputable def openCoefficientRestriction :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) :=
  (ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X) ⋙
    Mod.comap (asIso (condensedPullbackHom Λ j)).inv

/-- The specified extension-to-inverse-restriction collapse, natural in the module.
Source: def-sfb-comap-upper-star-iso.proof.md and extension-iso quotient normalization
(blueprint: lem-sfb-open-coefficient-square-action-identification). -/
noncomputable def openCoefficientCollapse :
    upperStar Λ j ≅ openCoefficientRestriction Λ j :=
  Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j))

/-- The collapse sends `x ⊗ n` to `α⁻¹(x)n` and its inverse inserts the unit.
Source: def-sfb-comap-upper-star-iso.proof.md, balanced-collapse identification
(blueprint: lem-sfb-open-coefficient-square-action-identification).

Proof: step 1 of the node applies lem-sfb-extension-iso-quotient-formula to α and
mapMod(j⁻¹)(N). Its quotient equation is the first clause and its unit-insertion formula
is the second; the comparison used there is exactly extendScalarsIsoComapInv. -/
theorem openCoefficientCollapse_quotient [IsOpenImmersion j]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.extendπ (condensedPullbackHom Λ j)
        (((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X)).obj N) ≫
        ((openCoefficientCollapse Λ j).hom.app N).hom =
      (asIso (condensedPullbackHom Λ j)).inv ▷ (ProEtale.upperStar Ab.{u + 1} j).obj N.X ≫
        γ[(ProEtale.upperStar Ab.{u + 1} j).obj (condensedRingObj Λ X),
          (ProEtale.upperStar Ab.{u + 1} j).obj N.X] ∧
    ((openCoefficientCollapse Λ j).inv.app N).hom =
      (λ_ ((ProEtale.upperStar Ab.{u + 1} j).obj N.X)).inv ≫
        η[condensedRingObj Λ U] ▷ (ProEtale.upperStar Ab.{u + 1} j).obj N.X ≫
        Mod.extendπ (condensedPullbackHom Λ j)
          (((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X)).obj N) := by
  have h := Mod.extensionIso_quotient_formula (condensedPullbackHom Λ j)
    (((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ X)).obj N)
  exact ⟨h.2.1, h.2.2.2.1⟩

variable {Λ}
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The inverse coefficient square, with neither coefficient change inverted.
Source: def-sfb-comap-upper-star-iso.proof.md, coefficient square
(blueprint: lem-sfb-open-coefficient-square-action-identification).

Proof: step 2 precomposes map_coefficientMap_comp_condensedPullbackHom with α_A⁻¹
and postcomposes with α_B⁻¹, then cancels both coefficient isomorphisms. -/
theorem openCoefficient_inverse_square [IsOpenImmersion j] :
    coefficientMap a U ≫ (asIso (condensedPullbackHom Λ' j)).inv =
      (asIso (condensedPullbackHom Λ j)).inv ≫
        (ProEtale.upperStar Ab.{u + 1} j).map (coefficientMap a X) := by
  have _ := (inferInstance : IsCommMonObj Λ)
  have _ := (inferInstance : IsCommMonObj Λ')
  have _ := (inferInstance : IsMonHom a)
  apply (cancel_epi (condensedPullbackHom Λ j)).1
  rw [← Category.assoc, ← map_coefficientMap_comp_condensedPullbackHom a j]
  simp only [asIso_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
    IsIso.hom_inv_id_assoc]

/-- The comparison between the two inverse-restriction descriptions; every factor keeps
underlying objects and arrows and has identity underlying components.
Source: def-sfb-comap-upper-star-iso.proof.md, transport and restriction comparison
(blueprint: lem-sfb-open-coefficient-square-action-identification). -/
noncomputable def openCoefficientIdentityRestrictionIso [IsOpenImmersion j] :
    Mod.comap (coefficientMap a X) ⋙ openCoefficientRestriction Λ j ≅
      openCoefficientRestriction Λ' j ⋙ Mod.comap (coefficientMap a U) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((ProEtale.upperStar Ab.{u + 1} j).mapModComapIso (coefficientMap a X))
      (Mod.comap (asIso (condensedPullbackHom Λ j)).inv) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ' X))
      ((Mod.comapComp (asIso (condensedPullbackHom Λ j)).inv
          ((ProEtale.upperStar Ab.{u + 1} j).map (coefficientMap a X))).symm ≪≫
        Mod.comapCongr (openCoefficient_inverse_square j a).symm ≪≫
        Mod.comapComp (coefficientMap a U) (asIso (condensedPullbackHom Λ' j)).inv) ≪≫
    (Functor.associator _ _ _).symm

/-- The identity action comparison d⁰ on the actual extension-based module pullbacks.
Source: def-sfb-comap-upper-star-iso.proof.md, balanced-collapse identifications
(blueprint: lem-sfb-open-coefficient-square-action-identification). -/
noncomputable def openCoefficientIdentityIso [IsOpenImmersion j] :
    Mod.comap (coefficientMap a X) ⋙ upperStar Λ j ≅
      upperStar Λ' j ⋙ Mod.comap (coefficientMap a U) :=
  Functor.isoWhiskerLeft (Mod.comap (coefficientMap a X)) (openCoefficientCollapse Λ j) ≪≫
    openCoefficientIdentityRestrictionIso j a ≪≫
    Functor.isoWhiskerRight (openCoefficientCollapse Λ' j).symm
      (Mod.comap (coefficientMap a U))

private lemma cancel_normalized_hom {C : Type*} [Category C] {W X Y Z : C}
    (s : W ⟶ X) (p : X ⟶ W) (t : W ⟶ Y) (q : Y ⟶ W)
    (f : Y ⟶ Z) (r : Z ⟶ W) (hs : s ≫ p = 𝟙 W) (ht : t ≫ q = 𝟙 W)
    (hf : f ≫ r = q) : s ≫ p ≫ t ≫ f ≫ r = 𝟙 W := by
  rw [hf, ht, Category.comp_id, hs]

private lemma cancel_normalized_inv {C : Type*} [Category C] {W X Y Z : C}
    (s : W ⟶ X) (p : X ⟶ W) (t : W ⟶ Y) (q : Y ⟶ W)
    (f : Y ⟶ Z) (r : Z ⟶ W) (hs : s ≫ p = 𝟙 W) (ht : t ≫ q = 𝟙 W)
    (hf : f ≫ r = q) : t ≫ f ≫ r ≫ s ≫ p = 𝟙 W := by
  rw [hs, Category.comp_id, hf, ht]

/-- Both normalized actions are the transported B_X-action restricted along the inverse square.
Source: def-sfb-comap-upper-star-iso.proof.md, action calculation
(blueprint: lem-sfb-open-coefficient-square-action-identification).

Proof: steps 3 and 4 expand mapMod and comap. Naturality of the monoidal structure
moves F(a_X) through μ. The inverse-square equation then identifies the two actions.
Steps 5 and 6 expand the published scalar-square comparison with its actual collapse
factors; its middle comap factors and the transport factor have underlying identity.
Cancellation gives both normalized component identities. The same computation on the
explicit inverse-restriction composite gives the two identities for d⁰. -/
theorem openCoefficientSquare_actions_components [IsOpenImmersion j]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    γ[condensedRingObj Λ U,
        ((openCoefficientRestriction Λ' j ⋙ Mod.comap (coefficientMap a U)).obj N).X] =
      (coefficientMap a U ≫ (asIso (condensedPullbackHom Λ' j)).inv) ▷
          (ProEtale.upperStar Ab.{u + 1} j).obj N.X ≫
        Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} j)
          (condensedRingObj Λ' X) N.X ≫
        (ProEtale.upperStar Ab.{u + 1} j).map γ[condensedRingObj Λ' X,N.X] ∧
    γ[condensedRingObj Λ U,
        ((Mod.comap (coefficientMap a X) ⋙ openCoefficientRestriction Λ j).obj N).X] =
      (coefficientMap a U ≫ (asIso (condensedPullbackHom Λ' j)).inv) ▷
          (ProEtale.upperStar Ab.{u + 1} j).obj N.X ≫
        Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} j)
          (condensedRingObj Λ' X) N.X ≫
        (ProEtale.upperStar Ab.{u + 1} j).map γ[condensedRingObj Λ' X,N.X] ∧
    ((openCoefficientCollapse Λ' j).inv.app N).hom ≫
        ((comapUpperStarIso a j).hom.app N).hom ≫
        ((openCoefficientCollapse Λ j).hom.app ((Mod.comap (coefficientMap a X)).obj N)).hom =
      𝟙 ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) ∧
    ((openCoefficientCollapse Λ j).inv.app ((Mod.comap (coefficientMap a X)).obj N)).hom ≫
        ((comapUpperStarIso a j).inv.app N).hom ≫
        ((openCoefficientCollapse Λ' j).hom.app N).hom =
      𝟙 ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) ∧
    ((openCoefficientIdentityRestrictionIso j a).hom.app N).hom =
      𝟙 ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) ∧
    ((openCoefficientIdentityRestrictionIso j a).inv.app N).hom =
      𝟙 ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change coefficientMap a U ▷ _ ≫
        (asIso (condensedPullbackHom Λ' j)).inv ▷ _ ≫
        Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} j) _ _ ≫
        (ProEtale.upperStar Ab.{u + 1} j).map γ[condensedRingObj Λ' X,N.X] = _
    rw [← comp_whiskerRight_assoc]
  · change (asIso (condensedPullbackHom Λ j)).inv ▷ _ ≫
        Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} j) _ _ ≫
        (ProEtale.upperStar Ab.{u + 1} j).map
          (coefficientMap a X ▷ N.X ≫ γ[condensedRingObj Λ' X,N.X]) = _
    rw [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc,
      ← comp_whiskerRight_assoc, ← openCoefficient_inverse_square j a]
  · let F := ProEtale.upperStar Ab.{u + 1} j
    let A := condensedRingObj Λ X
    let B := condensedRingObj Λ' X
    let e := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)
    let e' := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' j)
    let t := F.mapModComapIso (coefficientMap a X)
    let M := (F.mapMod B).obj N
    let M' := (F.mapMod A).obj ((Mod.comap (coefficientMap a X)).obj N)
    let M'' := (Mod.comap (F.map (coefficientMap a X))).obj M
    have hn := congrArg Mod.Hom.hom (e.hom.naturality (t.inv.app N))
    change ((Mod.extendScalars (condensedPullbackHom Λ j)).map
        (t.inv.app N)).hom ≫ (e.hom.app M').hom =
      (e.hom.app M'').hom ≫ 𝟙 (F.obj N.X) at hn
    have hn' := hn.trans (Category.comp_id (e.hom.app M'').hom)
    simp only [Functor.comp_obj,
      comapUpperStarIso, Mod.extendScalarsComapIsoOfIsIso,
      openCoefficientCollapse, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.symm_hom, Mod.comp_hom', Mod.id_hom',
      Mod.comap_map_hom, Mod.comapComp_hom_app_hom, Mod.comapComp_inv_app_hom,
      Mod.comapCongr, NatIso.ofComponents_hom_app,
      Mod.isoMk_hom_hom, Iso.refl_hom,
      Category.id_comp, Category.comp_id, Category.assoc]
    change (e'.inv.app M).hom ≫ (e'.hom.app M).hom ≫
      (e.inv.app M'').hom ≫
      ((Mod.extendScalars (condensedPullbackHom Λ j)).map (t.inv.app N)).hom ≫
      (e.hom.app M').hom = _
    have ha := congrArg Mod.Hom.hom (e.inv_hom_id_app M'')
    have hb := congrArg Mod.Hom.hom (e'.inv_hom_id_app M)
    change (e.inv.app M'').hom ≫ (e.hom.app M'').hom = 𝟙 (F.obj N.X) at ha
    change (e'.inv.app M).hom ≫ (e'.hom.app M).hom = 𝟙 (F.obj N.X) at hb
    exact cancel_normalized_hom (W := F.obj N.X)
      (X := ((Mod.extendScalars (condensedPullbackHom Λ' j)).obj M).X)
      (Y := ((Mod.extendScalars (condensedPullbackHom Λ j)).obj M'').X)
      (Z := ((Mod.extendScalars (condensedPullbackHom Λ j)).obj M').X)
      (e'.inv.app M).hom (e'.hom.app M).hom
      (e.inv.app M'').hom (e.hom.app M'').hom
      ((Mod.extendScalars (condensedPullbackHom Λ j)).map (t.inv.app N)).hom
      (e.hom.app M').hom hb ha hn'
  · let F := ProEtale.upperStar Ab.{u + 1} j
    let A := condensedRingObj Λ X
    let B := condensedRingObj Λ' X
    let e := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)
    let e' := Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' j)
    let t := F.mapModComapIso (coefficientMap a X)
    let M := (F.mapMod B).obj N
    let M' := (F.mapMod A).obj ((Mod.comap (coefficientMap a X)).obj N)
    let M'' := (Mod.comap (F.map (coefficientMap a X))).obj M
    have hn := congrArg Mod.Hom.hom (e.hom.naturality (t.hom.app N))
    change ((Mod.extendScalars (condensedPullbackHom Λ j)).map
        (t.hom.app N)).hom ≫ (e.hom.app M'').hom =
      (e.hom.app M').hom ≫ 𝟙 (F.obj N.X) at hn
    have hn' := hn.trans (Category.comp_id (e.hom.app M').hom)
    simp only [Functor.comp_obj,
      comapUpperStarIso, Mod.extendScalarsComapIsoOfIsIso,
      openCoefficientCollapse, Iso.trans_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.symm_inv, Mod.comp_hom', Mod.id_hom',
      Mod.comap_map_hom, Mod.comapComp_hom_app_hom, Mod.comapComp_inv_app_hom,
      Mod.comapCongr, NatIso.ofComponents_inv_app,
      Mod.isoMk_inv_hom, Iso.refl_inv,
      Category.id_comp, Category.comp_id, Category.assoc]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
    change (e.inv.app M').hom ≫
      ((Mod.extendScalars (condensedPullbackHom Λ j)).map (t.hom.app N)).hom ≫
      (e.hom.app M'').hom ≫ (e'.inv.app M).hom ≫ (e'.hom.app M).hom = _
    have ha := congrArg Mod.Hom.hom (e.inv_hom_id_app M')
    have hb := congrArg Mod.Hom.hom (e'.inv_hom_id_app M)
    change (e.inv.app M').hom ≫ (e.hom.app M').hom = 𝟙 (F.obj N.X) at ha
    change (e'.inv.app M).hom ≫ (e'.hom.app M).hom = 𝟙 (F.obj N.X) at hb
    exact cancel_normalized_inv (W := F.obj N.X)
      (X := ((Mod.extendScalars (condensedPullbackHom Λ' j)).obj M).X)
      (Y := ((Mod.extendScalars (condensedPullbackHom Λ j)).obj M').X)
      (Z := ((Mod.extendScalars (condensedPullbackHom Λ j)).obj M'').X)
      (e'.inv.app M).hom (e'.hom.app M).hom
      (e.inv.app M').hom (e.hom.app M').hom
      ((Mod.extendScalars (condensedPullbackHom Λ j)).map (t.hom.app N)).hom
      (e.hom.app M'').hom hb ha hn'
  · change (𝟙 _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _)) ≫ 𝟙 _ :
        (ProEtale.upperStar Ab.{u + 1} j).obj N.X ⟶ _) = _
    simp only [Category.id_comp]
  · change (𝟙 _ ≫ ((𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ :
        (ProEtale.upperStar Ab.{u + 1} j).obj N.X ⟶ _) = _
    simp only [Category.id_comp]

/-- Under both collapses, a morphism h is sent to Fh.
Source: def-sfb-comap-upper-star-iso.proof.md, naturality on module morphisms
(blueprint: lem-sfb-open-coefficient-square-action-identification).

Proof: steps 3, 4 and 6 use that comap keeps arrows, mapMod maps them by F, and the
collapse is a natural isomorphism. Its inverse cancels its forward component. -/
theorem openCoefficientSquare_maps [IsOpenImmersion j]
    {N M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)}
    (h : N ⟶ M) :
    ((openCoefficientCollapse Λ' j).inv.app N).hom ≫
        (((upperStar Λ' j ⋙ Mod.comap (coefficientMap a U)).map h).hom) ≫
        ((openCoefficientCollapse Λ' j).hom.app M).hom =
      (ProEtale.upperStar Ab.{u + 1} j).map h.hom ∧
    ((openCoefficientCollapse Λ j).inv.app ((Mod.comap (coefficientMap a X)).obj N)).hom ≫
        (((Mod.comap (coefficientMap a X) ⋙ upperStar Λ j).map h).hom) ≫
        ((openCoefficientCollapse Λ j).hom.app ((Mod.comap (coefficientMap a X)).obj M)).hom =
      (ProEtale.upperStar Ab.{u + 1} j).map h.hom := by
  constructor
  · have hn := (openCoefficientCollapse Λ' j).hom.naturality h
    have hc := congrArg Mod.Hom.hom hn
    change (((upperStar Λ' j ⋙ Mod.comap (coefficientMap a U)).map h).hom) ≫
        ((openCoefficientCollapse Λ' j).hom.app M).hom =
      ((openCoefficientCollapse Λ' j).hom.app N).hom ≫
        (ProEtale.upperStar Ab.{u + 1} j).map h.hom at hc
    rw [hc, ← Category.assoc]
    have hi := congrArg Mod.Hom.hom ((openCoefficientCollapse Λ' j).inv_hom_id_app N)
    change _ ≫ _ = 𝟙 _ at hi
    rw [hi, Category.id_comp]
  · have hn := (openCoefficientCollapse Λ j).hom.naturality
      ((Mod.comap (coefficientMap a X)).map h)
    have hc := congrArg Mod.Hom.hom hn
    change (((Mod.comap (coefficientMap a X) ⋙ upperStar Λ j).map h).hom) ≫
        ((openCoefficientCollapse Λ j).hom.app ((Mod.comap (coefficientMap a X)).obj M)).hom =
      ((openCoefficientCollapse Λ j).hom.app ((Mod.comap (coefficientMap a X)).obj N)).hom ≫
        (ProEtale.upperStar Ab.{u + 1} j).map h.hom at hc
    rw [hc, ← Category.assoc]
    have hi := congrArg Mod.Hom.hom ((openCoefficientCollapse Λ j).inv_hom_id_app
      ((Mod.comap (coefficientMap a X)).obj N))
    change _ ≫ _ = 𝟙 _ at hi
    rw [hi, Category.id_comp]

/-- The reverse of the specified ordinary comparison is d⁰ as a natural isomorphism.
Source: def-sfb-comap-upper-star-iso.proof.md, normalization of the prescribed composite
(blueprint: lem-sfb-open-coefficient-square-action-identification).

Proof: steps 5 and 6 expand extendScalarsComapIsoOfIsIso. Its extension comparisons
are the collapses by lem-sfb-extension-iso-quotient-formula. Its middle restriction
comparison and the mapModComapIso factor have identity underlying maps. Naturality
of the collapse gives the component identities, and the faithful forgetful functor
identifies the module maps with the explicitly constructed d⁰. -/
theorem comapUpperStarIso_symm_eq_openCoefficientIdentityIso [IsOpenImmersion j] :
    (comapUpperStarIso a j).symm = openCoefficientIdentityIso j a := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply Mod.hom_ext
  apply (cancel_epi
    ((openCoefficientCollapse Λ j).inv.app ((Mod.comap (coefficientMap a X)).obj N)).hom).1
  apply (cancel_mono ((openCoefficientCollapse Λ' j).hom.app N).hom).1
  have h := openCoefficientSquare_actions_components j a N
  have ha := congrArg Mod.Hom.hom ((openCoefficientCollapse Λ j).inv_hom_id_app
    ((Mod.comap (coefficientMap a X)).obj N))
  have hb := congrArg Mod.Hom.hom ((openCoefficientCollapse Λ' j).inv_hom_id_app N)
  change _ ≫ _ = 𝟙 ((ProEtale.upperStar Ab.{u + 1} j).obj N.X) at ha hb
  simp only [openCoefficientIdentityIso, Iso.symm_hom, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comap_map_hom, h.2.2.2.2.1, Category.assoc]
  rw [hb]
  erw [Category.comp_id]
  rw [ha]
  exact h.2.2.2.1

/-- Degreewise localization of the identity action comparison, with the published
composition factorization isomorphisms retained.
Source: def-sfb-derived-comap-upper-star-iso.proof.md
(blueprint: lem-sfb-open-coefficient-square-action-identification). -/
noncomputable def derivedOpenCoefficientIdentityIso [IsOpenImmersion j] :
    D(Mod.comap (coefficientMap a X)) ⋙ D(upperStar Λ j) ≅
      D(upperStar Λ' j) ⋙ D(Mod.comap (coefficientMap a U)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openCoefficientIdentityIso j a) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified derived comparison has inverse equal to the localized identity action
comparison, on the whole ordinary unbounded derived category and without flatness of a.
Source: def-sfb-derived-comap-upper-star-iso.proof.md
(blueprint: lem-sfb-open-coefficient-square-action-identification).

Proof: step 7 uses the existing exactness instances of the actual module pullbacks
(sk-def-sfb-module-pushforward-pullback) and scalar restrictions
(sk-def-sfb-change-of-scalars) to apply
lem-weil-pbc-exact-functor-derived-factorization. Step 8 applies d⁰ and c⁰ degreewise;
naturality on differentials makes these inverse chain isomorphisms, and naturality
on chain maps makes them natural. Step 9 uses the same composite factorization
isomorphisms as derivedComapUpperStarIso. Localization respects composition and
inverses, and its natural-transformation full faithfulness
(lem-weil-pbc-localization-universal-property) gives equality on the entire derived
category. No boundedness or K-flat replacement is used. -/
theorem openCoefficientSquare_action_identification [IsOpenImmersion j] :
    (derivedComapUpperStarIso a j).symm = derivedOpenCoefficientIdentityIso j a := by
  apply Iso.ext
  simp only [derivedComapUpperStarIso, derivedOpenCoefficientIdentityIso,
    ← comapUpperStarIso_symm_eq_openCoefficientIdentityIso j a,
    Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
