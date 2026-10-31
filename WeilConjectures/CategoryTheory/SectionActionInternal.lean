/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.RingObjectSheaf
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Preadditive.Basic
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Mathlib.Algebra.Group.Shrink
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-! # Normalized lifting of sectionwise actions

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, first two sentences;
the expanded proof of `lem-sfb-section-action-internal`.
(blueprint: lem-sfb-section-action-internal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonoidalClosed
namespace CategoryTheory

/-- Abelian sheafification on the essentially small site is left exact.
Source: Stacks 00WH and the sheafification in the node's setup
(blueprint: lem-sfb-section-action-internal).
Proof: replace the site by its small model in the coefficient universe and apply
`GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian`, then transport back
using `hasSheafifyEssentiallySmallSite`. -/
@[instance] theorem sfbSectionAction_hasSheafify
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} := by
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}

/-- The prescribed sheafification-local maps are stable under tensor.
Source: the sheaf tensor in the node's setup (blueprint: lem-sfb-section-action-internal).
Proof: use `presheaf_enrichedHoms_exist` for the essentially small site. The
presheaf tensor-Hom adjunction and the sheaf property of Hom into a sheaf show
stability under left tensor; symmetry gives stability under right tensor. -/
@[instance] theorem sfbSectionAction_isMonoidal
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : (J.W (A := AddCommGrpCat.{w})).IsMonoidal := by
  let h := presheaf_enrichedHoms_exist (C := C) (A := AddCommGrpCat.{w})
  let : ∀ F G : Cᵒᵖ ⥤ AddCommGrpCat.{w},
    Enriched.FunctorCategory.HasEnrichedHom AddCommGrpCat.{w} F G := h.1
  let : ∀ F G : Cᵒᵖ ⥤ AddCommGrpCat.{w},
    Enriched.FunctorCategory.HasFunctorEnrichedHom AddCommGrpCat.{w} F G := h.2
  infer_instance

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  (J : GrothendieckTopology C)

/-- Sectionwise module sheaves, using existing presheaf module objects and the
full subcategory of objects whose underlying abelian presheaf is a sheaf.
Source: the category specified in lem-sfb-section-action-internal
(blueprint: lem-sfb-section-action-internal). -/
abbrev sfbSectionModules (B : Cᵒᵖ ⥤ AddCommGrpCat.{w}) [MonObj B] :=
  ObjectProperty.FullSubcategory
    (fun M : Mod (Cᵒᵖ ⥤ AddCommGrpCat.{w}) B => Presheaf.IsSheaf J M.X)

/-- The unchanged underlying abelian sheaf of a sectionwise module.
Source: lem-sfb-section-action-internal, underlying-sheaf clause
(blueprint: lem-sfb-section-action-internal). -/
def sfbSectionUnderlying {B : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [MonObj B]
    (M : sfbSectionModules J B) : Sheaf J AddCommGrpCat.{w} :=
  ⟨M.obj.X, M.property⟩

/-- The canonical normalized lift of a natural action, using the specified tensor
comparison, sheafification, and counit; no module laws are needed to construct it.
Source: lem-sfb-section-action-internal, displayed gamma formula
(blueprint: lem-sfb-section-action-internal). -/
def sfbSectionActionLift (B P : Sheaf J AddCommGrpCat.{w})
    (β : B.obj ⊗ P.obj ⟶ P.obj) : B ⊗ P ⟶ P :=
  (sfbSheafTensor_comparison J B P).hom ≫
    (presheafToSheaf J AddCommGrpCat.{w}).map β ≫
    (sheafificationAdjunction J AddCommGrpCat.{w}).counit.app P

/-- The coefficient abelian sheaf with its existing canonical internal ring structure.
Source: det-def-sfb-ring-object-sheaf, applied to a commutative ring sheaf
(blueprint: lem-sfb-section-action-internal). -/
abbrev sfbSectionCoefficient (B : Sheaf J CommRingCat.{w}) : Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)

/-- The existing pointwise ring object on the coefficient presheaf.
Source: det-def-sfb-ring-object-sheaf and the sectionwise multiplication in the node
(blueprint: lem-sfb-section-action-internal). -/
instance sfbSectionCoefficient_presheafMonObj (B : Sheaf J CommRingCat.{w}) :
    MonObj (sfbSectionCoefficient J B).obj :=
  Functor.monObjCompForget₂
    (B.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})

/-- The functor specified by internal actions on the same underlying sheaves and the
linearity of the unchanged underlying maps. All its data is explicit.
Source: lem-sfb-section-action-internal, functor clause
(blueprint: lem-sfb-section-action-internal). -/
def sfbSectionLiftFunctor (B : Sheaf J CommRingCat.{w})
    (m : ∀ M : sfbSectionModules J (sfbSectionCoefficient J B).obj,
      ModObj (sfbSectionCoefficient J B) (sfbSectionUnderlying J M))
    (lin : ∀ {M N : sfbSectionModules J (sfbSectionCoefficient J B).obj} (f : M ⟶ N),
      (m M).smul ≫ (⟨f.hom.hom⟩ : sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) =
        sfbSectionCoefficient J B ◁ (⟨f.hom.hom⟩ :
          sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) ≫ (m N).smul) :
    sfbSectionModules J (sfbSectionCoefficient J B).obj ⥤
      Mod (Sheaf J AddCommGrpCat.{w}) (sfbSectionCoefficient J B) where
  obj M := { X := sfbSectionUnderlying J M, mod := m M }
  map f := { hom := ⟨f.hom.hom⟩, isModHom := ⟨lin f⟩ }
  map_id _M := Mod.hom_ext _ _ rfl
  map_comp _f _g := Mod.hom_ext _ _ rfl

/-- The sectionwise regular module on the given coefficient sheaf.
Source: lem-sfb-section-action-internal, final clause
(blueprint: lem-sfb-section-action-internal). -/
def sfbSectionRegular (B : Sheaf J CommRingCat.{w}) :
    sfbSectionModules J (sfbSectionCoefficient J B).obj :=
  ⟨Mod.regular (sfbSectionCoefficient J B).obj, (sfbSectionCoefficient J B).property⟩

@[instance_reducible] private def presheafModule (B : Sheaf J CommRingCat.{w})
    (P : Sheaf J AddCommGrpCat.{w})
    (β : (sfbSectionCoefficient J B).obj ⊗ P.obj ⟶ P.obj)
    (hu : ∀ (U : Cᵒᵖ) (n : ℤ) (x : P.obj.obj U),
      (β.app U).hom ((n • (1 : B.obj.obj U)) ⊗ₜ[ℤ] x) = n • x)
    (ha : ∀ (U : Cᵒᵖ) (b c : B.obj.obj U) (x : P.obj.obj U),
      (β.app U).hom ((b * c) ⊗ₜ[ℤ] x) =
        (β.app U).hom (b ⊗ₜ[ℤ] (β.app U).hom (c ⊗ₜ[ℤ] x))) :
    ModObj (sfbSectionCoefficient J B).obj P.obj :=
  ModObj.mk' _ β (by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.toIntLinearMap_injective
    apply TensorProduct.ext'
    intro n x
    change (β.app U).hom
      (((MonObj.one (X := (sfbSectionCoefficient J B).obj)).app U).hom n ⊗ₜ[ℤ] x) =
      n.down • x
    convert hu U n.down x using 1
    congr 1
    congr 1
    change ((AddCommGrpCat.ringMonObj (B.obj.obj U)).one).hom n = n.down • 1
    exact (AddCommGrpCat.ringMonObj_one_apply _ n).trans (by simp)) (by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.toIntLinearMap_injective
    apply TensorProduct.ext_threefold
    intro b c x
    exact ha U b c x)

@[instance_reducible] private def liftModule (B : Sheaf J CommRingCat.{w})
    (P : Sheaf J AddCommGrpCat.{w})
    [ModObj (sfbSectionCoefficient J B).obj P.obj] :
    ModObj (sfbSectionCoefficient J B) P := by
  let S := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B
  let m : ModObj (Sheaf.sheafifyRingPresheaf J S.obj)
      ((presheafToSheaf J AddCommGrpCat.{w}).obj P.obj) :=
    (presheafToSheaf J AddCommGrpCat.{w}).modObjObj
      (A := (sfbSectionCoefficient J B).obj) P.obj
  exact @ModObj.ofIso _ _ _ _ _ _ (Sheaf.sheafifyRingPresheaf J S.obj) _
    ((presheafToSheaf J AddCommGrpCat.{w}).obj P.obj) (sfbSectionCoefficient J B) _
    (Sheaf.sheafifyRingPresheafIso J
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B))
    inferInstance P
    (asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app P)) m

private theorem liftModule_action (B : Sheaf J CommRingCat.{w})
    (P : Sheaf J AddCommGrpCat.{w})
    [ModObj (sfbSectionCoefficient J B).obj P.obj] :
    (liftModule J B P).smul = sfbSectionActionLift J (sfbSectionCoefficient J B) P
      (Mod.act (A := (sfbSectionCoefficient J B).obj) P.obj) := by
  change (inv ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app
      (sfbSectionCoefficient J B)) ⊗ₘ
      inv ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app P)) ≫
      (Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{w})
        (sfbSectionCoefficient J B).obj P.obj ≫
      (presheafToSheaf J AddCommGrpCat.{w}).map
        (Mod.act (A := (sfbSectionCoefficient J B).obj) P.obj)) ≫ _ = _
  unfold sfbSectionActionLift sfbSheafTensor_comparison
  simp only [Iso.trans_hom, tensorIso_hom, Category.assoc]
  rfl

private theorem liftModule_restrict (B : Sheaf J CommRingCat.{w})
    (P : Sheaf J AddCommGrpCat.{w})
    [ModObj (sfbSectionCoefficient J B).obj P.obj] :
    Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
        (sfbSectionCoefficient J B) P ≫ (liftModule J B P).smul.hom =
      Mod.act (A := (sfbSectionCoefficient J B).obj) P.obj := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{w}
  let e := asIso (adj.counit.app (sfbSectionCoefficient J B))
  let d := asIso (adj.counit.app P)
  have hμ : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
      (sfbSectionCoefficient J B) P = adj.homEquiv _ _
        (Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{w})
          (sfbSectionCoefficient J B).obj P.obj ≫ (e.hom ⊗ₘ d.hom)) := rfl
  have hm : (liftModule J B P).smul = (e.inv ⊗ₘ d.inv) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{w})
        (sfbSectionCoefficient J B).obj P.obj ≫
      (presheafToSheaf J AddCommGrpCat.{w}).map
        (Mod.act (A := (sfbSectionCoefficient J B).obj) P.obj) ≫ d.hom := rfl
  have key : (Functor.OplaxMonoidal.δ (presheafToSheaf J AddCommGrpCat.{w})
      (sfbSectionCoefficient J B).obj P.obj ≫ (e.hom ⊗ₘ d.hom)) ≫
      (e.inv ⊗ₘ d.inv) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{w})
        (sfbSectionCoefficient J B).obj P.obj ≫
      (presheafToSheaf J AddCommGrpCat.{w}).map
        (Mod.act (A := (sfbSectionCoefficient J B).obj) P.obj) ≫ d.hom =
      (presheafToSheaf J AddCommGrpCat.{w}).map
        (Mod.act (A := (sfbSectionCoefficient J B).obj) P.obj) ≫ d.hom := by
    erw [Category.assoc, tensorHom_comp_tensorHom_assoc, e.hom_inv_id, d.hom_inv_id,
      id_tensorHom_id, Category.id_comp, Functor.Monoidal.δ_μ_assoc]
  change _ ≫ (sheafToPresheaf J AddCommGrpCat.{w}).map (liftModule J B P).smul = _
  rw [hμ, hm, Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp, key,
    Functor.map_comp]
  erw [adj.unit_naturality_assoc, adj.right_triangle_components]
  exact Category.comp_id _

@[instance_reducible] private def underlyingModule {B' : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [MonObj B']
    (M : sfbSectionModules J B') : ModObj B' (sfbSectionUnderlying J M).obj := M.obj.mod

attribute [local instance] underlyingModule

private theorem liftModule_linear (B : Sheaf J CommRingCat.{w})
    (M N : sfbSectionModules J (sfbSectionCoefficient J B).obj)
    (f : sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) :
    (liftModule J B (sfbSectionUnderlying J M)).smul ≫ f =
        sfbSectionCoefficient J B ◁ f ≫ (liftModule J B (sfbSectionUnderlying J N)).smul ↔
      Mod.act (A := (sfbSectionCoefficient J B).obj) M.obj.X ≫ f.hom =
        (sfbSectionCoefficient J B).obj ◁ f.hom ≫
          Mod.act (A := (sfbSectionCoefficient J B).obj) N.obj.X := by
  have key : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
        (sfbSectionCoefficient J B) (sfbSectionUnderlying J M) ≫
        ((liftModule J B (sfbSectionUnderlying J M)).smul ≫ f).hom =
      Mod.act (A := (sfbSectionCoefficient J B).obj) M.obj.X ≫ f.hom := by
    change _ ≫ _ ≫ f.hom = _
    rw [← Category.assoc, liftModule_restrict]
  have key' : Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
        (sfbSectionCoefficient J B) (sfbSectionUnderlying J M) ≫
        (sfbSectionCoefficient J B ◁ f ≫
          (liftModule J B (sfbSectionUnderlying J N)).smul).hom =
      (sfbSectionCoefficient J B).obj ◁ f.hom ≫
        Mod.act (A := (sfbSectionCoefficient J B).obj) N.obj.X := by
    change _ ≫ (sheafToPresheaf J AddCommGrpCat.{w}).map (_ ◁ f) ≫ _ = _
    erw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [liftModule_restrict]
    rfl
  constructor
  · intro h
    rw [← key, ← key', h]
  · intro h
    apply Sheaf.tensor_hom_ext
    exact key.trans (h.trans key'.symm)

variable {B : Sheaf J CommRingCat.{w}}

private abbrev productGroup {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (U : Cᵒᵖ) :=
  Shrink.{w} (∀ i : I, (P i).obj.X.obj U)

private def productEquiv {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (U : Cᵒᵖ) :
    productGroup J P U ≃+ ∀ i : I, (P i).obj.X.obj U := Shrink.addEquiv

private def productPresheaf {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (productGroup J P U)
  map {U V} f := AddCommGrpCat.ofHom
    ((productEquiv J P V).symm.toAddMonoidHom.comp
      ((AddMonoidHom.pi fun i => ((P i).obj.X.map f).hom.comp
        (Pi.evalAddMonoidHom _ i)).comp (productEquiv J P U).toAddMonoidHom))
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (productEquiv J P U).injective
    funext i
    simp [productEquiv]
  map_comp {U V W} f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (productEquiv J P W).injective
    funext i
    simp [productEquiv, Functor.map_comp]

private theorem productPresheaf_map {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (productPresheaf J P).obj U) (i : I) :
    productEquiv J P V (((productPresheaf J P).map f).hom x) i =
      ((P i).obj.X.map f).hom (productEquiv J P U x i) := by
  exact congrFun ((productEquiv J P V).apply_symm_apply _) i

private def productProjection {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (i : I) :
    productPresheaf J P ⟶ (P i).obj.X where
  app U := AddCommGrpCat.ofHom
    ((Pi.evalAddMonoidHom _ i).comp (productEquiv J P U).toAddMonoidHom)
  naturality U V f := by
    ext x
    exact productPresheaf_map J P f x i

private def productCone {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    Fan (fun i => (P i).obj.X) :=
  Fan.mk (productPresheaf J P) (productProjection J P)

private def productConeIsLimit {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    IsLimit (productCone J P) := by
  refine Fan.IsLimit.mk _ (fun s => ?_) ?_ ?_
  · exact
      { app := fun U => AddCommGrpCat.ofHom
          ((productEquiv J P U).symm.toAddMonoidHom.comp
            (AddMonoidHom.pi fun i => ((s.π.app ⟨i⟩).app U).hom))
        naturality := fun U V f => by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          apply (productEquiv J P V).injective
          funext i
          simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
          dsimp only [productCone, Fan.mk] at *
          erw [productPresheaf_map]
          change productEquiv J P V ((productEquiv J P V).symm _) i =
            ((P i).obj.X.map f).hom (productEquiv J P U ((productEquiv J P U).symm _) i)
          rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
          exact ConcreteCategory.congr_hom ((s.π.app ⟨i⟩).naturality f) x }
  · intro s i
    ext U x
    exact congrFun ((productEquiv J P U).apply_symm_apply _) i
  · intro s m hm
    ext U x
    apply (productEquiv J P U).injective
    funext i
    have h := ConcreteCategory.congr_hom (congr_app (hm i) U) x
    change productEquiv J P U ((m.app U).hom x) i = _ at h
    change productEquiv J P U ((m.app U).hom x) i =
      productEquiv J P U ((productEquiv J P U).symm _) i
    rw [AddEquiv.apply_symm_apply]
    exact h

private def productModuleCone {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    Cone (Discrete.functor (fun i => (P i).obj) ⋙
      Mod.forget (sfbSectionCoefficient J B).obj) :=
  (Cone.postcompose (Discrete.compNatIsoDiscrete (fun i => (P i).obj)
    (Mod.forget (sfbSectionCoefficient J B).obj)).inv).obj (productCone J P)

private def productModuleConeIsLimit {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    IsLimit (productModuleCone J P) :=
  (IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete (fun i => (P i).obj)
    (Mod.forget (sfbSectionCoefficient J B).obj)) _).symm (productConeIsLimit J P)

private abbrev sectionProduct {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    sfbSectionModules J (sfbSectionCoefficient J B).obj := by
  let K := Discrete.functor (fun i => (P i).obj)
  let c : Cone (K ⋙ Mod.forget (sfbSectionCoefficient J B).obj) := productModuleCone J P
  let hc : IsLimit c := productModuleConeIsLimit J P
  let m := Mod.limitModObj K hc
  refine ⟨{ X := productPresheaf J P, mod := m }, ?_⟩
  exact Sheaf.isSheaf_of_isLimit
    (Discrete.functor (fun i => sfbSectionUnderlying J (P i)))
    ((Cone.postcompose (Discrete.compNatIsoDiscrete
      (fun i => sfbSectionUnderlying J (P i)) (sheafToPresheaf J AddCommGrpCat.{w})).inv).obj
        (productCone J P))
    ((IsLimit.postcomposeInvEquiv (Discrete.compNatIsoDiscrete
      (fun i => sfbSectionUnderlying J (P i)) (sheafToPresheaf J AddCommGrpCat.{w}))
      (productCone J P)).symm (productConeIsLimit J P))

private abbrev sectionProductProjection {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) (i : I) :
    sectionProduct J P ⟶ P i := by
  let K := Discrete.functor (fun i => (P i).obj)
  let c : Cone (K ⋙ Mod.forget (sfbSectionCoefficient J B).obj) := productModuleCone J P
  let hc : IsLimit c := productModuleConeIsLimit J P
  exact ⟨(Mod.liftedLimitCone K hc).π.app ⟨i⟩⟩

private def sectionProductSheafLimit {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    IsLimit (Fan.mk (sfbSectionUnderlying J (sectionProduct J P))
      (fun i => (⟨(sectionProductProjection J P i).hom.hom⟩ :
        sfbSectionUnderlying J (sectionProduct J P) ⟶ sfbSectionUnderlying J (P i)))) := by
  apply isLimitOfIsLimitFanMkObj (sheafToPresheaf J AddCommGrpCat.{w})
  change IsLimit (Fan.mk (productPresheaf J P)
    (fun i => (sectionProductProjection J P i).hom.hom))
  have h (i : I) : (sectionProductProjection J P i).hom.hom =
      productProjection J P i := by
    change productProjection J P i ≫ 𝟙 ((P i).obj.X) = productProjection J P i
    exact Category.comp_id _
  rw [show (fun i => (sectionProductProjection J P i).hom.hom) =
    productProjection J P from funext h]
  exact productConeIsLimit J P

private def sectionProductModuleLimit (B : Sheaf J CommRingCat.{w})
    (m : ∀ M : sfbSectionModules J (sfbSectionCoefficient J B).obj,
      ModObj (sfbSectionCoefficient J B) (sfbSectionUnderlying J M))
    (lin : ∀ {M N : sfbSectionModules J (sfbSectionCoefficient J B).obj} (f : M ⟶ N),
      (m M).smul ≫ (⟨f.hom.hom⟩ : sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) =
        sfbSectionCoefficient J B ◁ (⟨f.hom.hom⟩ :
          sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) ≫ (m N).smul)
    {I : Type t} [Finite I]
    (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj) :
    IsLimit (Fan.mk ((sfbSectionLiftFunctor J B m lin).obj (sectionProduct J P))
      (fun i => (sfbSectionLiftFunctor J B m lin).map (sectionProductProjection J P i))) := by
  apply isLimitOfIsLimitFanMkObj (Mod.forget (sfbSectionCoefficient J B))
  exact sectionProductSheafLimit J P

/-- A natural action on an abelian sheaf lifts uniquely by the counit formula;
the lift is unital and associative, detects linearity, and assembles additively
on unchanged sheaves and maps. Finite coordinate products lift to products for
all internal source modules, the empty product is zero and terminal, and the
regular action lifts to the prescribed ring multiplication.

Source: blueprint main-20261015, lem-sfb-subfield-flat.proof.md, first two sentences,
and the eight proof steps of lem-sfb-section-action-internal
(blueprint: lem-sfb-section-action-internal).

Proof:
1. The sheafification adjunction (def-weil-pbc-sheafification) identifies maps out
of a sheafification with presheaf maps. Naturality of its unit and the triangle
identity show that the displayed lift restricts to beta; uniqueness follows.
2. The sectionwise laws give a presheaf ModObj: compare the unit equation on
n tensor x and the associative equation on (b tensor c) tensor x.
3. Apply the existing lax-monoidal module transport to strong monoidal sheafification.
Transport its coefficient and module objects along their counit isomorphisms using
ModObj.ofIso. The coefficient monoid is exactly the prescribed ring structure.
The resulting action is the displayed normalized lift, so its module laws follow
from transport rather than a second coherence calculation.
4. Restrict the internal linearity equation along the tensor comparison. Its two
sides become the stated presheaf action-commuting equation. Uniqueness proves the
iff, using sk-def-sfb-module-objects for the meaning of internal linearity.
5. Identities, composites, sums, and zero maps commute with the actions by
bilinearity. The construction on maps is unchanged, hence defines an additive functor.
6. Construct the coordinate product presheaf, using Shrink on its section groups
so the independent universe of the finite index type is respected. Its tuple maps
prove the product universal property. Limits of sheaves are sheaves.
7. Apply lem-sfb-modobj-forget-creates first in presheaves to obtain its action.
Its linear projections give the coordinate action formula. Apply limit reflection
for internal modules to the underlying sheaf product cone; this proves the product
property for arbitrary internal sources. When the index is empty, the limiting
cone is terminal, and a terminal abelian sheaf is zero.
8. The ring multiplication and the lift of its pointwise multiplication extend
the same map, so uniqueness identifies them. This is the regular module.
-/
theorem sfbSectionActionInternal (B : Sheaf J CommRingCat.{w}) :
    (∀ (P : Sheaf J AddCommGrpCat.{w})
      (β : (sfbSectionCoefficient J B).obj ⊗ P.obj ⟶ P.obj),
      (∀ (U : Cᵒᵖ) (n : ℤ) (x : P.obj.obj U),
        (β.app U).hom ((n • (1 : B.obj.obj U)) ⊗ₜ[ℤ] x) = n • x) →
      (∀ (U : Cᵒᵖ) (b c : B.obj.obj U) (x : P.obj.obj U),
        (β.app U).hom ((b * c) ⊗ₜ[ℤ] x) =
          (β.app U).hom (b ⊗ₜ[ℤ] (β.app U).hom (c ⊗ₜ[ℤ] x))) →
      ∃ m : ModObj (sfbSectionCoefficient J B) P,
        m.smul = sfbSectionActionLift J (sfbSectionCoefficient J B) P β ∧
        Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
            (sfbSectionCoefficient J B) P ≫ m.smul.hom = β ∧
        (∀ g : sfbSectionCoefficient J B ⊗ P ⟶ P,
          Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w})
              (sfbSectionCoefficient J B) P ≫ g.hom = β → g = m.smul)) ∧
    (∃ (m : ∀ M : sfbSectionModules J (sfbSectionCoefficient J B).obj,
        ModObj (sfbSectionCoefficient J B) (sfbSectionUnderlying J M))
      (lin : ∀ {M N : sfbSectionModules J (sfbSectionCoefficient J B).obj} (f : M ⟶ N),
        (m M).smul ≫ (⟨f.hom.hom⟩ : sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) =
          sfbSectionCoefficient J B ◁ (⟨f.hom.hom⟩ :
            sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) ≫ (m N).smul),
      (∀ M : sfbSectionModules J (sfbSectionCoefficient J B).obj,
        (m M).smul = sfbSectionActionLift J (sfbSectionCoefficient J B)
          (sfbSectionUnderlying J M) (Mod.act (A := (sfbSectionCoefficient J B).obj) M.obj.X)) ∧
      (∀ (M N : sfbSectionModules J (sfbSectionCoefficient J B).obj)
        (f : sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N),
        (m M).smul ≫ f = sfbSectionCoefficient J B ◁ f ≫ (m N).smul ↔
          Mod.act (A := (sfbSectionCoefficient J B).obj) M.obj.X ≫ f.hom = (sfbSectionCoefficient
            J B).obj ◁ f.hom ≫
            Mod.act (A := (sfbSectionCoefficient J B).obj) N.obj.X) ∧
      (sfbSectionLiftFunctor J B m lin).Additive ∧
      (∀ (I : Type t) [Finite I]
        (P : I → sfbSectionModules J (sfbSectionCoefficient J B).obj),
        ∃ (L : sfbSectionModules J (sfbSectionCoefficient J B).obj)
          (π : ∀ i : I, L ⟶ P i)
          (e : ∀ U : Cᵒᵖ, L.obj.X.obj U ≃+ ∀ i : I, (P i).obj.X.obj U),
          (∀ (i : I) (U : Cᵒᵖ) (x : L.obj.X.obj U),
            ((π i).hom.hom.app U).hom x = e U x i) ∧
          (∀ (U V : Cᵒᵖ) (f : U ⟶ V) (x : L.obj.X.obj U) (i : I),
            e V ((L.obj.X.map f).hom x) i = ((P i).obj.X.map f).hom (e U x i)) ∧
          (∀ (U : Cᵒᵖ) (b : B.obj.obj U) (x : L.obj.X.obj U) (i : I),
            e U (((Mod.act (A := (sfbSectionCoefficient J B).obj) L.obj.X).app U).hom (b ⊗ₜ[ℤ] x))
            i =
              ((Mod.act (A := (sfbSectionCoefficient J B).obj) (P i).obj.X).app U).hom (b ⊗ₜ[ℤ] e
            U x i)) ∧
          Nonempty (IsLimit (Fan.mk (sfbSectionUnderlying J L)
            (fun i => (⟨(π i).hom.hom⟩ :
              sfbSectionUnderlying J L ⟶ sfbSectionUnderlying J (P i))))) ∧
          Nonempty (IsLimit (Fan.mk ((sfbSectionLiftFunctor J B m lin).obj L)
            (fun i => (sfbSectionLiftFunctor J B m lin).map (π i)))) ∧
          (IsEmpty I → IsZero (sfbSectionUnderlying J L) ∧
            Nonempty (IsTerminal ((sfbSectionLiftFunctor J B m lin).obj L)))) ∧
      (m (sfbSectionRegular J B)).smul = MonObj.mul (X := sfbSectionCoefficient J B)) := by
  classical
  constructor
  · intro P β hu ha
    let : ModObj (sfbSectionCoefficient J B).obj P.obj := presheafModule J B P β hu ha
    refine ⟨liftModule J B P, liftModule_action J B P, liftModule_restrict J B P, ?_⟩
    intro g hg
    exact Sheaf.tensor_hom_ext (hg.trans (liftModule_restrict J B P).symm)
  · let m := fun M : sfbSectionModules J (sfbSectionCoefficient J B).obj =>
      liftModule J B (sfbSectionUnderlying J M)
    have lin : ∀ {M N : sfbSectionModules J (sfbSectionCoefficient J B).obj} (f : M ⟶ N),
        (m M).smul ≫ (⟨f.hom.hom⟩ : sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) =
          sfbSectionCoefficient J B ◁ (⟨f.hom.hom⟩ :
            sfbSectionUnderlying J M ⟶ sfbSectionUnderlying J N) ≫ (m N).smul := by
      intro M N f
      exact (liftModule_linear J B M N ⟨f.hom.hom⟩).2 (Mod.act_hom f.hom)
    refine ⟨m, lin, fun M => liftModule_action J B _,
      fun M N f => liftModule_linear J B M N f, ?_, ?_, ?_⟩
    · constructor
      intro M N f g
      apply Mod.hom_ext
      apply Sheaf.hom_ext
      rfl
    · intro I _ P
      refine ⟨sectionProduct J P, sectionProductProjection J P, productEquiv J P,
        (fun _ _ _ => by simp [Mod.liftedLimitCone,
          productModuleCone, productCone, productProjection, Mod.homMk]),
        (fun _ _ => productPresheaf_map J P), ?_,
        ⟨sectionProductSheafLimit J P⟩, ⟨sectionProductModuleLimit J B m lin P⟩, ?_⟩
      · intro U b x i
        exact ConcreteCategory.congr_hom
          (congr_app (Mod.act_hom (sectionProductProjection J P i).hom) U) (b ⊗ₜ[ℤ] x)
      · intro hI
        let : IsEmpty I := hI
        have ht := (isLimitEquivIsTerminalOfIsEmpty _ _)
          (sectionProductModuleLimit J B m lin P)
        refine ⟨?_, ⟨ht⟩⟩
        exact ((isLimitEquivIsTerminalOfIsEmpty _ _)
          (sectionProductSheafLimit J P)).isZero
    · apply Sheaf.tensor_hom_ext
      exact (liftModule_restrict J B (sfbSectionUnderlying J (sfbSectionRegular J B))).trans
        (Sheaf.μ_comp_map_mul (sfbSectionCoefficient J B)).symm

end CategoryTheory
