/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementConstruction
import all WeilConjectures.SixFunctors.OpenTensorNormalizationData
import all WeilConjectures.AlgebraicGeometry.NativeConstantRestrictionAcyclicity
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Existence of finite section-preserving realizations

The diagram-site module equivalence and the constant inverse-image ring map construct
these realizations.  The proof is retained as a named obligation for the coefficient
supplement assembly.

(blueprint: new-lem-pur-ringed-refinement-finite-realization-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

-- Keep this proof cache transparent so its coefficient universe can be inferred.
set_option linter.defProp false in
@[instance_reducible]
private def ringCompose {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  hasSheafCompose_of_preservesLimitsOfSize (J := J)
    (F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 2000000] ringCompose

private theorem systemsTopology (X : Scheme.{u}) :
    topology .systems X = WeilConjectures.coefficientSequenceTopology (ProEt.topology X) := by
  rw [topology_systems_eq]
  apply GrothendieckTopology.ext
  rfl

private local instance sndContinuous (X : Scheme.{u}) :
    (CategoryTheory.Prod.snd ℕ X.ProEt).IsContinuous
      (topology .systems X) (ProEt.topology X) := by
  constructor
  intro F
  rw [topology_systems_eq]
  apply (verticalSheaf_iff X.ProEt (ProEt.topology X) _).2
  intro n
  exact (isSheaf_iff_isSheaf_of_type _ _).1 F.property

private local instance sndCocontinuous (X : Scheme.{u}) :
    (CategoryTheory.Prod.snd ℕ X.ProEt).IsCocontinuous
      (topology .systems X) (ProEt.topology X) := by
  constructor
  intro V S hS
  rw [topology_systems_eq]
  exact hS

private local instance sndRightKan (X : Scheme.{u})
    (F : (Site .systems X)ᵒᵖ ⥤ CommRingCat.{u + 1}) :
    (CategoryTheory.Prod.snd ℕ X.ProEt).op.HasPointwiseRightKanExtension F := by
  infer_instance

private def verticalRing (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    Rings .systems X :=
  ((CategoryTheory.Prod.snd ℕ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (topology .systems X) (ProEt.topology X)).obj
      (ProEtale.StrictTower.coefficients.{u} B X)

private def verticalRingIso (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    finiteRing B X ≅ verticalRing B X :=
  ((CategoryTheory.Prod.snd ℕ X.ProEt).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} (topology .systems X) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))

set_option maxHeartbeats 2000000 in
-- The sheafification unit equation unfolds the two presentations of the vertical site.
private theorem verticalRingIso_scalar (B : Type (u + 1)) [CommRing B]
    (X : Scheme.{u}) (n : ℕ) (Z : X.ProEt) (a : B) :
    (verticalRingIso B X).hom.hom.app (op (n, Z)) (finiteSystemScalar B X n Z a) =
      finiteScalar B X Z a := by
  exact ConcreteCategory.congr_hom (congr_app
    ((CategoryTheory.Prod.snd ℕ X.ProEt).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{u + 1} (topology .systems X) (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))) (op (n, Z))) a

private def topologyModulesEquivalence {C : Type (u + 1)} [Category.{u} C]
    {J K : GrothendieckTopology C} (h : J = K) (R : Cᵒᵖ ⥤ RingCat.{u + 1})
    (hJ : Presheaf.IsSheaf J R) (hK : Presheaf.IsSheaf K R) :
    SheafOfModules.{u + 1} (⟨R, hJ⟩ : Sheaf J RingCat.{u + 1}) ≌
      SheafOfModules.{u + 1} (⟨R, hK⟩ : Sheaf K RingCat.{u + 1}) where
  functor :=
    { obj M := ⟨M.val,
        (congrArg (fun L ↦ Presheaf.IsSheaf L M.val.presheaf) h).mp M.isSheaf⟩
      map f := ⟨f.val⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse :=
    { obj M := ⟨M.val,
        (congrArg (fun L ↦ Presheaf.IsSheaf L M.val.presheaf) h).mpr M.isSheaf⟩
      map f := ⟨f.val⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  functor_unitIso_comp _ := rfl

private def verticalRebundle (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    Mod.{u} (verticalRing B X) ≌
      SheafOfModules.{u + 1, u, u + 1, u + 1}
        (WeilConjectures.NativeConstantModel.sequenceRing.{u + 1, u, u + 1}
          (ProEt.topology X)
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (ProEtale.StrictTower.coefficients.{u} B X))) :=
  @topologyModulesEquivalence.{u} (ℕ × X.ProEt) inferInstance
    (topology .systems X) (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))
    (systemsTopology X)
    ((CategoryTheory.Prod.snd ℕ X.ProEt).op ⋙
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (ProEtale.StrictTower.coefficients.{u} B X)).obj)
    ((sheafCompose (topology .systems X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (verticalRing B X)).property
    (WeilConjectures.NativeConstantModel.sequenceRing.{u + 1, u, u + 1}
      (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (ProEtale.StrictTower.coefficients.{u} B X))).property

private def verticalEquivalence (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    Mod.{u} (verticalRing B X) ≌ ProEtale.StrictTower.Towers B X :=
  (verticalRebundle B X).trans
    (WeilConjectures.NativeConstantModel.sequenceEquivalence.{u + 1, u, u + 1} (ProEt.topology X)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (ProEtale.StrictTower.coefficients.{u} B X)))

private def scalarEquivalence {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) :
    Mod S ≌ Mod R := by
  let d := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso e
  have : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (CategoryTheory.Equivalence.refl (C := C)) d.hom d.inv
    (by
      change Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ))
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj =
          d.inv.hom ≫ d.hom.hom
      rw [Functor.whiskerRight_id']
      exact (congrArg (fun f ↦ f.hom) d.inv_hom_id).symm)
    (by
      change d.hom.hom ≫ d.inv.hom ≫ Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ))
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj = 𝟙 _
      rw [Functor.whiskerRight_id']
      change d.hom.hom ≫ d.inv.hom ≫ 𝟙 _ = 𝟙 _
      rw [Category.comp_id]
      exact congrArg (fun f ↦ f.hom) d.hom_inv_id)

private def realizationEquivalence (B : Type (u + 1)) [CommRing B] (X : Scheme.{u})
    {R : Rings .systems X} (c : R ≅ finiteRing B X) :
    ProEtale.StrictTower.Towers B X ≌ Mod R :=
  (verticalEquivalence B X).symm.trans (scalarEquivalence (c ≪≫ verticalRingIso B X))

private theorem realizationAdditive (B : Type (u + 1)) [CommRing B] (X : Scheme.{u})
    {R : Rings .systems X} (c : R ≅ finiteRing B X) :
    (realizationEquivalence B X c).functor.Additive where
  map_add := by intro N M f g; ext Z x; rfl

private def realizationUnderlying (B : Type (u + 1)) [CommRing B] (X : Scheme.{u})
    {R : Rings .systems X} (c : R ≅ finiteRing B X) :
    (realizationEquivalence B X c).functor ⋙ additivePresheaf R ≅ towerPresheaf B X :=
  NatIso.ofComponents (fun N ↦ NatIso.ofComponents (fun Z ↦ Iso.refl _) (by
    intro Z Z' f
    ext x
    rfl)) (by intro N M f; ext Z x; rfl)

private theorem realizationScalar (B : Type (u + 1)) [CommRing B] (X : Scheme.{u})
    {R : Rings .systems X} (c : R ≅ finiteRing B X)
    (N : ProEtale.StrictTower.Towers B X) (n : ℕ) (Z : X.ProEt) (a : B)
    (x : ((realizationEquivalence B X c).functor.obj N).val.obj (op (n, Z))) :
    ((realizationUnderlying B X c).hom.app N).app (op (n, Z))
      (c.inv.hom.app (op (n, Z)) (finiteSystemScalar B X n Z a) • x) =
      @SMul.smul ((ProEtale.StrictTower.coefficients.{u} B X).obj.obj (op Z))
        ((N.obj (op n)).val.obj (op Z)) inferInstance (finiteScalar B X Z a)
        (((realizationUnderlying B X c).hom.app N).app (op (n, Z)) x) := by
  change @SMul.smul ((ProEtale.StrictTower.coefficients.{u} B X).obj.obj (op Z))
    ((N.obj (op n)).val.obj (op Z)) inferInstance
    ((verticalRingIso B X).hom.hom.app (op (n, Z))
      (c.hom.hom.app (op (n, Z))
        (c.inv.hom.app (op (n, Z)) (finiteSystemScalar B X n Z a)))) x = _
  have hc (y : (finiteRing B X).obj.obj (op (n, Z))) :
      c.hom.hom.app (op (n, Z)) (c.inv.hom.app (op (n, Z)) y) = y :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun f ↦ f.hom) c.inv_hom_id)
      (op (n, Z))) y
  rw [hc, verticalRingIso_scalar]
  rfl

set_option maxHeartbeats 2000000 in
-- Comparing the concrete sheaf adjunctions requires unfolding their section presentations.
private theorem finiteInverse_isIso (B : Type (u + 1)) [CommRing B]
    {U T : Scheme.{u}} (f : U ⟶ T) : IsIso (finiteInverse B f) := by
  let G := baseChange .systems f
  have : (proEtaleBaseChange f).Final := inferInstance
  have : G.Final := inferInstanceAs (((𝟭 ℕ).prod (proEtaleBaseChange f)).Final)
  let A := CommRingCat.{u + 1}
  let J := topology .systems T
  let K := topology .systems U
  let aJ : constantSheaf J A ⊣ sheafToPresheaf J A ⋙ lim :=
    (constLimAdj (J := (Site .systems T)ᵒᵖ) (C := A)).comp
      (sheafificationAdjunction J A)
  let aK : constantSheaf K A ⊣ sheafToPresheaf K A ⋙ lim :=
    (constLimAdj (J := (Site .systems U)ᵒᵖ) (C := A)).comp
      (sheafificationAdjunction K A)
  let e : G.sheafPushforwardContinuous A J K ⋙ (sheafToPresheaf J A ⋙ lim) ≅
      sheafToPresheaf K A ⋙ lim :=
    Functor.isoWhiskerLeft (sheafToPresheaf K A) (Functor.Initial.limIso G.op)
  let a := (aJ.comp (ringAdjunction .systems f)).ofNatIsoRight e
  have he : finiteInverse B f = (a.leftAdjointUniq aK).hom.app (CommRingCat.of B) := by
    apply (a.homEquiv _ _).injective
    trans aK.unit.app (CommRingCat.of B)
    swap
    · exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a aK (CommRingCat.of B)).symm
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (aJ.comp (ringAdjunction .systems f)).homEquiv _ _
      (((ringAdjunction .systems f).homEquiv _ _).symm (finiteDirect B f)) ≫
        e.hom.app (finiteRing B U) = _
    rw [Adjunction.comp_homEquiv]
    change (aJ.homEquiv _ _)
      (((ringAdjunction .systems f).homEquiv (finiteRing B T) (finiteRing B U))
        (((ringAdjunction .systems f).homEquiv (finiteRing B T)
          (finiteRing B U)).symm (finiteDirect B f))) ≫
        e.hom.app (finiteRing B U) = _
    have hc := ((ringAdjunction .systems f).homEquiv (finiteRing B T)
      (finiteRing B U)).apply_symm_apply (finiteDirect B f)
    trans (aJ.homEquiv _ _ (finiteDirect B f)) ≫ e.hom.app (finiteRing B U)
    · exact congrArg (fun k ↦ (aJ.homEquiv _ _ k) ≫ e.hom.app (finiteRing B U)) hc
    apply (cancel_mono (e.inv.app (finiteRing B U))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply limit.hom_ext
    intro Z
    simp only [ObjectProperty.ι_obj, Functor.comp_obj, lim_obj, constLimAdj,
      Functor.const_obj_obj, Functor.id_obj, Adjunction.comp_homEquiv,
      Adjunction.mk'_homEquiv, finiteDirect, Equiv.trans_apply, Equiv.coe_fn_mk,
      Category.assoc, Adjunction.comp_unit_app, Adjunction.mk'_unit,
      sheafificationAdjunction_unit_app, lim_map, limit.lift_map, Functor.Initial.limIso,
      Functor.Initial.limitIso, Iso.symm_symm_eq, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
      Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
      Functor.whiskeringLeft_obj_obj, asIso_hom, aJ, aK, e]
    change limit.lift (G.op ⋙ (finiteRing B U).obj)
      ⟨CommRingCat.of B, ((sheafificationAdjunction J A).homEquiv
        ((Functor.const (Site .systems T)ᵒᵖ).obj (CommRingCat.of B))
        ((G.sheafPushforwardContinuous A J K).obj (finiteRing B U)))
        (((sheafificationAdjunction J A).homEquiv
          ((Functor.const (Site .systems T)ᵒᵖ).obj (CommRingCat.of B))
          ((G.sheafPushforwardContinuous A J K).obj (finiteRing B U))).symm
          (Functor.whiskerLeft G.op (toSheafify K
            ((Functor.const (Site .systems U)ᵒᵖ).obj (CommRingCat.of B)))))⟩ ≫
        𝟙 _ ≫ limit.π (G.op ⋙ (finiteRing B U).obj) Z =
      limit.lift (finiteRing B U).obj
        ((Cone.postcompose (toSheafify K
          ((Functor.const (Site .systems U)ᵒᵖ).obj (CommRingCat.of B)))).obj
            ⟨CommRingCat.of B, 𝟙 _⟩) ≫
        limit.pre (finiteRing B U).obj G.op ≫
          limit.π (G.op ⋙ (finiteRing B U).obj) Z
    rw [Equiv.apply_symm_apply]
    simp
  -- Transfer invertibility from the component of the normalized adjoint isomorphism.
  rw [he]
  infer_instance

/-- The section-preserving finite realization exists at every object over `T`.

Source: coefficient supplement Step 10; Stacks 00Z4, 0H7J and 03D1.
The proof constructs the vertical product site realization, transports modules along
its constant inverse-image ring isomorphism, and verifies the section and scalar
normalizations componentwise.  It is a genuine construction for the arbitrary
ringed refinement package, not an arbitrary witness of existence.

(blueprint: new-lem-pur-ringed-refinement-finite-realization-exists).
-/
theorem finiteRealization_exists {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B] :
    Nonempty (∀ W : Over T, FiniteRealization P B W) := by
  classical
  refine ⟨fun W ↦ ?_⟩
  letI := finiteInverse_isIso B W.hom
  let c := asIso (finiteInverse B W.hom)
  exact {
    equivalence := realizationEquivalence B W.left c
    additive := realizationAdditive B W.left c
    underlying := realizationUnderlying B W.left c
    constant := c
    constant_hom := rfl
    scalar := realizationScalar B W.left c }

end SheafOfModules.RingedRefinement
