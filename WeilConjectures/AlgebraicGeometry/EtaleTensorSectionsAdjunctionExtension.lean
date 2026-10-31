/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Adjunction extension of maps from étale tensor sections

Source: Stacks Project, Descent, Tag 070S (2), omitted small-site proof;
Sheaves, Tag 0096 (blueprint: lem-trf-etale-tensor-sections-adjunction-extension).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Opens of an étale scheme, viewed as objects over the base by composition.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionOpenFunctor {T V : Scheme.{u}} (f : V ⟶ T) [hf : Etale f] :
    V.Opens ⥤ T.Etale :=
  gabberOpenEtale V ⋙ MorphismProperty.Over.map ⊤ hf

/-- Precompose module presheaves with the open-subscheme functor, restricting scalars
along the canonical open-section ring identification.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionZariskiPresheaf {T V : Scheme.{u}} (f : V ⟶ T) [Etale f] :
    _root_.PresheafOfModules.{u}
        (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
      _root_.PresheafOfModules.{u} V.ringCatSheaf.obj :=
  _root_.PresheafOfModules.pushforward (F := tensorExtensionOpenFunctor f)
    (Functor.whiskerRight V.restrictFunctorΓ.inv (forget₂ CommRingCat.{u} RingCat.{u}))

/-- Restriction to the opens of V, with its actual structure-ring scalar action.
The ring sheaf is the existing regular-function sheaf composed with forgetting to rings.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionZariskiRestriction {T V : Scheme.{u}} (f : V ⟶ T) [hf : Etale f]
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf) : V.Modules :=
  letI := gabberOpenEtale_continuous V
  letI : (MorphismProperty.Over.map ⊤ hf).IsContinuous
      V.smallEtaleTopology T.smallEtaleTopology :=
    Scheme.isContinuous_overMap (P := @Etale) (Q := @Etale) hf le_rfl
  letI : (tensorExtensionOpenFunctor f).IsContinuous
      (Opens.grothendieckTopology V) T.smallEtaleTopology :=
    Functor.isContinuous_comp (gabberOpenEtale V)
      (MorphismProperty.Over.map ⊤ hf) (Opens.grothendieckTopology V)
      V.smallEtaleTopology T.smallEtaleTopology
  { val := (tensorExtensionZariskiPresheaf f).obj G
    isSheaf := (tensorExtensionOpenFunctor f).op_comp_isSheaf_of_isSheaf
      (Opens.grothendieckTopology V) T.smallEtaleTopology G.presheaf hG }

/-- Identify the top open of V over T with the étale object f itself.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionTopIso {T V : Scheme.{u}} (f : V ⟶ T) [hf : Etale f] :
    (tensorExtensionOpenFunctor f).obj ⊤ ≅ Scheme.Etale.mk f :=
  (MorphismProperty.Over.map ⊤ hf).mapIso (gabberTopEtaleIso V) ≪≫
    MorphismProperty.Over.isoMk (Iso.refl V) (Category.id_comp f)

/-- Identify an open over T composed with its identity with the open itself.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionBaseOpenIso (T : Scheme.{u}) (W : T.Opens) :
    (tensorExtensionOpenFunctor (𝟙 T)).obj W ≅ Scheme.Etale.mk W.ι :=
  MorphismProperty.Over.isoMk (Iso.refl W.toScheme) (Category.comp_id W.ι).symm

/-- The arrow V_W to W in the original small étale site.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionBaseChangeArrow {T V : Scheme.{u}} (f : V ⟶ T) [Etale f]
    (W : T.Opens) :
    (tensorExtensionOpenFunctor f).obj (f ⁻¹ᵁ W) ⟶
      (tensorExtensionOpenFunctor (𝟙 T)).obj W :=
  MorphismProperty.Over.homMk (f ∣_ W)
    ((Category.assoc (f ∣_ W) W.ι (𝟙 T)).symm.trans
      ((congrArg (fun a ↦ a ≫ 𝟙 T) (morphismRestrict_ι f W)).trans
        (Category.comp_id _)))

/-- Restriction of a module-sheaf map to the Zariski opens of an étale scheme.
Source: Stacks 070S (2) (blueprint: lem-trf-etale-tensor-sections-adjunction-extension). -/
def tensorExtensionZariskiMap {T V : Scheme.{u}} (f : V ⟶ T) [Etale f]
    {G G' : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (hG' : Presheaf.IsSheaf T.smallEtaleTopology G'.presheaf) (k : G ⟶ G') :
    tensorExtensionZariskiRestriction f G hG ⟶ tensorExtensionZariskiRestriction f G' hG' :=
  ⟨(tensorExtensionZariskiPresheaf f).map k⟩

attribute [local irreducible] tensorPullback tensorPullbackObj

private def extensionAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ⊣ pushforward f :=
  Classical.choose (exists_tensorPullbackAdjunction f)

private theorem extensionScalarSquare {T V : Scheme.{u}} (f : V ⟶ T) (W : T.Opens) :
    T.restrictFunctorΓ.inv.app (op W) ≫ (f ∣_ W).appTop =
      f.app W ≫ V.restrictFunctorΓ.inv.app (op (f ⁻¹ᵁ W)) := by
  change T.presheaf.map (eqToHom W.ι_image_top).op ≫ (f ∣_ W).appTop =
    f.app W ≫ V.presheaf.map (eqToHom (f ⁻¹ᵁ W).ι_image_top).op
  rw [morphismRestrict_appTop, ← Category.assoc, f.naturality]
  rw [Category.assoc, ← V.presheaf.map_comp]
  congr 1

private def extensionBaseMap {T V : Scheme.{u}} (f : V ⟶ T) [Etale f]
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (M : T.Modules) (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) :
    M ⟶ (pushforward f).obj (tensorExtensionZariskiRestriction f G hG) where
  val :=
    { app := fun W ↦ ModuleCat.ofHom (X := M.val.obj W)
        (Y := ((pushforward f).obj (tensorExtensionZariskiRestriction f G hG)).val.obj W)
        { toFun := fun m ↦ G.map (tensorExtensionBaseChangeArrow f W.unop).op
            (β.app W.unop m)
          map_add' := by intros; simp only [map_add]
          map_smul' := by
            intro r m
            rw [Hom.app_smul]
            change G.map (tensorExtensionBaseChangeArrow f W.unop).op
                ((T.restrictFunctorΓ.inv.app W r) •
                  (show G.obj (op ((tensorExtensionOpenFunctor (𝟙 T)).obj W.unop))
                    from β.app W.unop m)) = _
            rw [G.map_smul]
            have hr : (f ∣_ W.unop).appTop (T.restrictFunctorΓ.inv.app W r) =
                V.restrictFunctorΓ.inv.app (op (f ⁻¹ᵁ W.unop)) (f.app W.unop r) :=
              ConcreteCategory.congr_hom (extensionScalarSquare f W.unop) r
            change (f ∣_ W.unop).appTop (T.restrictFunctorΓ.inv.app W r) •
                (show G.obj (op ((tensorExtensionOpenFunctor f).obj (f ⁻¹ᵁ W.unop)))
                  from G.map (tensorExtensionBaseChangeArrow f W.unop).op (β.app W.unop m)) =
              V.restrictFunctorΓ.inv.app (op (f ⁻¹ᵁ W.unop)) (f.app W.unop r) •
                (show G.obj (op ((tensorExtensionOpenFunctor f).obj (f ⁻¹ᵁ W.unop)))
                  from G.map (tensorExtensionBaseChangeArrow f W.unop).op (β.app W.unop m))
            rw [hr] }
      naturality := by
        intro W W' i
        ext m
        change G.map (tensorExtensionBaseChangeArrow f W'.unop).op
            (β.app W'.unop (M.val.map i m)) = _
        rw [show β.app W'.unop (M.val.map i m) =
            (tensorExtensionZariskiRestriction (𝟙 T) G hG).val.map i (β.app W.unop m)
          from PresheafOfModules.naturality_apply β.val i m]
        change G.presheaf.map (tensorExtensionBaseChangeArrow f W'.unop).op
            (G.presheaf.map ((tensorExtensionOpenFunctor (𝟙 T)).map i.unop).op
              (β.app W.unop m)) =
          G.presheaf.map ((tensorExtensionOpenFunctor f).map
              ((Opens.map f.base).map i.unop)).op
            (G.presheaf.map (tensorExtensionBaseChangeArrow f W.unop).op
              (β.app W.unop m))
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← G.presheaf.map_comp, ← G.presheaf.map_comp, ← op_comp, ← op_comp]
        apply congrArg (fun e :
          (tensorExtensionOpenFunctor f).obj (f ⁻¹ᵁ W'.unop) ⟶
            (tensorExtensionOpenFunctor (𝟙 T)).obj W.unop ↦
              G.presheaf.map e.op (β.app W.unop m))
        apply MorphismProperty.Over.Hom.ext
        exact morphismRestrict_homOfLE f _ _ i.unop.le }

private theorem extensionBaseMap_naturality {T : Scheme.{u}} (U : T.Etale)
    (M' M : T.Modules)
    (G G' : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (hG' : Presheaf.IsSheaf T.smallEtaleTopology G'.presheaf)
    (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG)
    (h : M' ⟶ M) (k : G ⟶ G') :
    extensionBaseMap U.hom G' hG' M'
        (h ≫ β ≫ tensorExtensionZariskiMap (𝟙 T) hG hG' k) =
      h ≫ extensionBaseMap U.hom G hG M β ≫
        (pushforward U.hom).map (tensorExtensionZariskiMap U.hom hG hG' k) := by
  apply hom_ext
  intro W
  ext m
  change G'.map (tensorExtensionBaseChangeArrow U.hom W).op
      (k.app (op ((tensorExtensionOpenFunctor (𝟙 T)).obj W))
        (β.app W (h.app W m))) =
    k.app (op ((tensorExtensionOpenFunctor U.hom).obj (U.hom ⁻¹ᵁ W)))
      (G.map (tensorExtensionBaseChangeArrow U.hom W).op (β.app W (h.app W m)))
  exact (PresheafOfModules.naturality_apply k
    (tensorExtensionBaseChangeArrow U.hom W).op _).symm

private def extensionComponent {T : Scheme.{u}} (M : T.Modules)
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) (U : T.Etale) :
    Γ((tensorPullback U.hom).obj M, ⊤) ⟶ G.presheaf.obj (op U) :=
  (((extensionAdj U.hom).homEquiv M
    (tensorExtensionZariskiRestriction U.hom G hG)).symm
      (extensionBaseMap U.hom G hG M β)).app ⊤ ≫
    G.presheaf.map (tensorExtensionTopIso U.hom).inv.op

private theorem extensionComponent_naturality {T : Scheme.{u}}
    (M' M : T.Modules)
    (G G' : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (hG' : Presheaf.IsSheaf T.smallEtaleTopology G'.presheaf)
    (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG)
    (h : M' ⟶ M) (k : G ⟶ G') (U : T.Etale) :
    extensionComponent M' G' hG'
        (h ≫ β ≫ tensorExtensionZariskiMap (𝟙 T) hG hG' k) U =
      ((tensorPullback U.hom).map h).app ⊤ ≫ extensionComponent M G hG β U ≫
        ((PresheafOfModules.toPresheaf _).map k).app (op U) := by
  unfold extensionComponent
  rw [extensionBaseMap_naturality,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Hom.comp_app, Category.assoc]
  congr 1
  ext s
  change G'.map (tensorExtensionTopIso U.hom).inv.op
      (k.app (op ((tensorExtensionOpenFunctor U.hom).obj ⊤)) _) =
    k.app (op U) (G.map (tensorExtensionTopIso U.hom).inv.op _)
  exact (PresheafOfModules.naturality_apply k
    (tensorExtensionTopIso U.hom).inv.op _).symm

private theorem extensionTopRing {T : Scheme.{u}} (U : T.Etale) :
    U.left.restrictFunctorΓ.inv.app (op ⊤) ≫
      (tensorExtensionTopIso U.hom).inv.left.appTop = 𝟙 _ := by
  have htop : U.left.restrictFunctorΓ.inv.app (op ⊤) =
      (tensorExtensionTopIso U.hom).hom.left.appTop := by
    change U.left.presheaf.map (eqToHom (⊤ : U.left.Opens).ι_image_top).op =
      ((⊤ : U.left.Opens).ι ≫ 𝟙 U.left).appTop
    rw [Category.comp_id, Scheme.Opens.ι_appTop]
    congr 2
  rw [htop, ← Scheme.Hom.comp_appTop]
  have hi : (tensorExtensionTopIso U.hom).inv.left ≫
      (tensorExtensionTopIso U.hom).hom.left = 𝟙 U.left :=
    congrArg (fun f ↦ f.left) (tensorExtensionTopIso U.hom).inv_hom_id
  rw [hi, Scheme.Hom.id_appTop]

private theorem extensionComponent_smul {T : Scheme.{u}} (M : T.Modules)
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG)
    (U : T.Etale) (r : Γ(U.left, ⊤)) (s : Γ((tensorPullback U.hom).obj M, ⊤)) :
    extensionComponent M G hG β U ((((tensorPullback U.hom).obj M).smul r).hom s) =
      r • (show G.obj (op U) from extensionComponent M G hG β U s) := by
  unfold extensionComponent
  simp only [ConcreteCategory.comp_apply, smul_apply, Hom.app_smul]
  change G.map (tensorExtensionTopIso U.hom).inv.op
      ((U.left.restrictFunctorΓ.inv.app (op ⊤) r) •
        (show G.obj (op ((tensorExtensionOpenFunctor U.hom).obj ⊤)) from _)) = _
  rw [G.map_smul]
  exact congrArg (fun a ↦ a • G.map (tensorExtensionTopIso U.hom).inv.op
    ((((extensionAdj U.hom).homEquiv M
      (tensorExtensionZariskiRestriction U.hom G hG)).symm
        (extensionBaseMap U.hom G hG M β)).app ⊤ s))
    (ConcreteCategory.congr_hom (extensionTopRing U) r)

private def extensionTriangleArrow {T V V' : Scheme.{u}}
    (f : V' ⟶ V) (u : V ⟶ T) (v : V' ⟶ T) [Etale u] [Etale v]
    (h : f ≫ u = v) (W : V.Opens) :
    (tensorExtensionOpenFunctor v).obj (f ⁻¹ᵁ W) ⟶
      (tensorExtensionOpenFunctor u).obj W :=
  MorphismProperty.Over.homMk (f ∣_ W) (by
    change (f ∣_ W) ≫ W.ι ≫ u = (f ⁻¹ᵁ W).ι ≫ v
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, h])

private def extensionTriangleMap {T V V' : Scheme.{u}}
    (f : V' ⟶ V) (u : V ⟶ T) (v : V' ⟶ T) [Etale u] [Etale v]
    (h : f ≫ u = v)
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf) :
    tensorExtensionZariskiRestriction u G hG ⟶
      (pushforward f).obj (tensorExtensionZariskiRestriction v G hG) where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        (X := (tensorExtensionZariskiRestriction u G hG).val.obj W)
        (Y := ((pushforward f).obj (tensorExtensionZariskiRestriction v G hG)).val.obj W)
        { toFun := fun m ↦ G.map (extensionTriangleArrow f u v h W.unop).op m
          map_add' := map_add _
          map_smul' := by
            intro r m
            change G.map (extensionTriangleArrow f u v h W.unop).op
              ((V.restrictFunctorΓ.inv.app W r) •
                (show G.obj (op ((tensorExtensionOpenFunctor u).obj W.unop)) from m)) = _
            rw [G.map_smul]
            have hr : (f ∣_ W.unop).appTop (V.restrictFunctorΓ.inv.app W r) =
                V'.restrictFunctorΓ.inv.app (op (f ⁻¹ᵁ W.unop)) (f.app W.unop r) :=
              ConcreteCategory.congr_hom (extensionScalarSquare f W.unop) r
            change (f ∣_ W.unop).appTop (V.restrictFunctorΓ.inv.app W r) •
                (show G.obj (op ((tensorExtensionOpenFunctor v).obj (f ⁻¹ᵁ W.unop)))
                  from G.map (extensionTriangleArrow f u v h W.unop).op m) =
              V'.restrictFunctorΓ.inv.app (op (f ⁻¹ᵁ W.unop)) (f.app W.unop r) •
                (show G.obj (op ((tensorExtensionOpenFunctor v).obj (f ⁻¹ᵁ W.unop)))
                  from G.map (extensionTriangleArrow f u v h W.unop).op m)
            rw [hr] }
      naturality := by
        intro W W' i
        ext m
        change G.presheaf.map (extensionTriangleArrow f u v h W'.unop).op
            (G.presheaf.map ((tensorExtensionOpenFunctor u).map i.unop).op m) =
          G.presheaf.map ((tensorExtensionOpenFunctor v).map
              ((Opens.map f.base).map i.unop)).op
            (G.presheaf.map (extensionTriangleArrow f u v h W.unop).op m)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← G.presheaf.map_comp, ← G.presheaf.map_comp, ← op_comp, ← op_comp]
        apply congrArg (fun e :
          (tensorExtensionOpenFunctor v).obj (f ⁻¹ᵁ W'.unop) ⟶
            (tensorExtensionOpenFunctor u).obj W.unop ↦ G.presheaf.map e.op m)
        apply MorphismProperty.Over.Hom.ext
        exact morphismRestrict_homOfLE f _ _ i.unop.le }

private theorem extensionBaseMap_triangle {T V V' : Scheme.{u}}
    (f : V' ⟶ V) (u : V ⟶ T) [Etale u] [Etale (f ≫ u)]
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (M : T.Modules) (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) :
    extensionBaseMap u G hG M β ≫
        (pushforward u).map (extensionTriangleMap f u (f ≫ u) rfl G hG) =
      extensionBaseMap (f ≫ u) G hG M β ≫
        (pushforwardComp f u).inv.app (tensorExtensionZariskiRestriction (f ≫ u) G hG) := by
  apply hom_ext
  intro W
  ext m
  change G.presheaf.map (extensionTriangleArrow f u (f ≫ u) rfl (u ⁻¹ᵁ W)).op
      (G.presheaf.map (tensorExtensionBaseChangeArrow u W).op (β.app W m)) =
    G.presheaf.map (tensorExtensionBaseChangeArrow (f ≫ u) W).op (β.app W m)
  rw [← ConcreteCategory.comp_apply, ← G.presheaf.map_comp, ← op_comp]
  apply congrArg (fun e : (tensorExtensionOpenFunctor (f ≫ u)).obj ((f ≫ u) ⁻¹ᵁ W) ⟶
    (tensorExtensionOpenFunctor (𝟙 T)).obj W ↦ G.presheaf.map e.op (β.app W m))
  apply MorphismProperty.Over.Hom.ext
  exact (morphismRestrict_comp f u W).symm

private theorem extensionComp_homEquiv {A B C : Scheme.{u}}
    (f : A ⟶ B) (u : B ⟶ C) (M : C.Modules) (N : A.Modules)
    (a : (tensorPullback (f ≫ u)).obj M ⟶ N) :
    (((extensionAdj u).comp
      (extensionAdj f)).homEquiv M N)
        ((tensorSectionsComp f u).hom.app M ≫ a) =
      ((extensionAdj (f ≫ u)).homEquiv M N) a ≫
        (pushforwardComp f u).inv.app N := by
  let adj := extensionAdj (f ≫ u)
  let adj' := (extensionAdj u).comp
    (extensionAdj f)
  have hu := unit_conjugateEquiv_symm adj adj' (pushforwardComp f u).inv M
  change adj.unit.app M ≫ (pushforwardComp f u).inv.app _ =
    adj'.unit.app M ≫ (pushforward f ⋙ pushforward u).map
      ((tensorSectionsComp f u).hom.app M) at hu
  change (adj'.homEquiv M N) _ = (adj.homEquiv M N) a ≫ _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc, ← (pushforwardComp f u).inv.naturality a,
    ← Category.assoc, ← Adjunction.homEquiv_unit]

private theorem extensionOpenUnit_aux (T : Scheme.{u}) (M : T.Modules) (W : T.Opens)
    (L : T.Modules ⥤ W.toScheme.Modules) (adj : L ⊣ pushforward W.ι) :
    (adj.unit.app M).app W ≫
        (L.obj M).presheaf.map (eqToHom W.ι_preimage_self.symm).op ≫
        ((adj.leftAdjointUniq (restrictAdjunction W.ι)).hom.app M).app ⊤ ≫
        M.presheaf.map (eqToHom W.ι_image_top.symm).op = 𝟙 _ := by
  let e := (adj.leftAdjointUniq (restrictAdjunction W.ι)).hom.app M
  have hu := congrArg (fun f ↦ f.app W)
    (adj.unit_leftAdjointUniq_hom_app (restrictAdjunction W.ι) M)
  change (adj.unit.app M).app W ≫ e.app (W.ι ⁻¹ᵁ W) =
    M.presheaf.map (homOfLE (W.ι.image_preimage_le W)).op at hu
  have hn := e.mapPresheaf.naturality (eqToHom W.ι_preimage_self.symm).op
  change (L.obj M).presheaf.map (eqToHom W.ι_preimage_self.symm).op ≫ e.app ⊤ =
    e.app (W.ι ⁻¹ᵁ W) ≫ ((restrictFunctor W.ι).obj M).presheaf.map
      (eqToHom W.ι_preimage_self.symm).op at hn
  change (adj.unit.app M).app W ≫
    ((L.obj M).presheaf.map (eqToHom W.ι_preimage_self.symm).op ≫ e.app ⊤) ≫
      M.presheaf.map (eqToHom W.ι_image_top.symm).op = 𝟙 _
  rw [hn]
  simp only [← Category.assoc]
  rw [hu]
  rw [restrict_map]
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  trans M.presheaf.map (𝟙 (op W))
  · exact congrArg M.presheaf.map (Subsingleton.elim _ _)
  · exact M.presheaf.map_id _

set_option backward.isDefEq.respectTransparency true in
private theorem extensionOpenUnit (T : Scheme.{u}) (M : T.Modules) (W : T.Opens) :
    (tensorOpenSectionIso T M W).inv =
      ((extensionAdj W.ι).unit.app M).app W ≫
        ((tensorPullback W.ι).obj M).presheaf.map (eqToHom W.ι_preimage_self.symm).op := by
  apply (cancel_mono (tensorOpenSectionIso T M W).hom).mp
  rw [Iso.inv_hom_id]
  symm
  exact extensionOpenUnit_aux T M W (tensorPullback W.ι) (extensionAdj W.ι)

private theorem extensionComponent_open {T : Scheme.{u}} (M : T.Modules)
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG)
    (W : T.Opens) (m : Γ(M, W)) :
    extensionComponent M G hG β (Scheme.Etale.mk W.ι)
        ((tensorOpenSectionIso T M W).inv m) =
      G.presheaf.map (tensorExtensionBaseOpenIso T W).inv.op (β.app W m) := by
  let adj := extensionAdj W.ι
  let a := (adj.homEquiv M (tensorExtensionZariskiRestriction W.ι G hG)).symm
    (extensionBaseMap W.ι G hG M β)
  have ha : adj.unit.app M ≫ (pushforward W.ι).map a =
      extensionBaseMap W.ι G hG M β := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have has := congrArg (fun f ↦ f.app W m) ha
  change a.app (W.ι ⁻¹ᵁ W) ((adj.unit.app M).app W m) =
    G.presheaf.map (tensorExtensionBaseChangeArrow W.ι W).op (β.app W m) at has
  have hn := a.mapPresheaf.naturality (eqToHom W.ι_preimage_self.symm).op
  have hns := ConcreteCategory.congr_hom hn ((adj.unit.app M).app W m)
  change a.app ⊤ (((tensorPullback W.ι).obj M).presheaf.map
        (eqToHom W.ι_preimage_self.symm).op ((adj.unit.app M).app W m)) =
    (tensorExtensionZariskiRestriction W.ι G hG).presheaf.map
      (eqToHom W.ι_preimage_self.symm).op
      (a.app (W.ι ⁻¹ᵁ W) ((adj.unit.app M).app W m)) at hns
  unfold extensionComponent
  rw [extensionOpenUnit]
  change G.presheaf.map (tensorExtensionTopIso W.ι).inv.op
    (a.app ⊤ (((tensorPullback W.ι).obj M).presheaf.map
      (eqToHom W.ι_preimage_self.symm).op ((adj.unit.app M).app W m))) = _
  rw [hns, has]
  change G.presheaf.map (tensorExtensionTopIso W.ι).inv.op
      (G.presheaf.map ((tensorExtensionOpenFunctor W.ι).map
        (eqToHom W.ι_preimage_self.symm)).op
        (G.presheaf.map (tensorExtensionBaseChangeArrow W.ι W).op (β.app W m))) = _
  simp only [← ConcreteCategory.comp_apply, ← G.presheaf.map_comp, ← op_comp]
  apply congrArg (fun e : Scheme.Etale.mk W.ι ⟶
    (tensorExtensionOpenFunctor (𝟙 T)).obj W ↦ G.presheaf.map e.op (β.app W m))
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono W.ι).mp
  have h₁ := MorphismProperty.Over.w
    ((tensorExtensionTopIso W.ι).inv ≫
      (tensorExtensionOpenFunctor W.ι).map (eqToHom W.ι_preimage_self.symm) ≫
      tensorExtensionBaseChangeArrow W.ι W)
  have h₂ := MorphismProperty.Over.w (tensorExtensionBaseOpenIso T W).inv
  change _ ≫ (W.ι ≫ 𝟙 T) = W.ι at h₁ h₂
  simpa only [Category.comp_id] using h₁.trans h₂.symm

private theorem extensionTranspose_triangle {T V V' : Scheme.{u}}
    (f : V' ⟶ V) (u : V ⟶ T) [Etale u] [Etale (f ≫ u)]
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (M : T.Modules) (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) :
    let Nu := tensorExtensionZariskiRestriction u G hG
    let Nv := tensorExtensionZariskiRestriction (f ≫ u) G hG
    let au := ((extensionAdj u).homEquiv M Nu).symm
      (extensionBaseMap u G hG M β)
    let av := ((extensionAdj (f ≫ u)).homEquiv M Nv).symm
      (extensionBaseMap (f ≫ u) G hG M β)
    ((extensionAdj f).homEquiv
        ((tensorPullback u).obj M) Nv) ((tensorSectionsComp f u).hom.app M ≫ av) =
      au ≫ extensionTriangleMap f u (f ≫ u) rfl G hG := by
  dsimp only
  apply ((extensionAdj u).homEquiv M _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have hc := extensionComp_homEquiv f u M
    (tensorExtensionZariskiRestriction (f ≫ u) G hG)
    (((extensionAdj (f ≫ u)).homEquiv M
      (tensorExtensionZariskiRestriction (f ≫ u) G hG)).symm
        (extensionBaseMap (f ≫ u) G hG M β))
  rw [Adjunction.comp_homEquiv] at hc
  simp only [Equiv.apply_symm_apply] at hc
  exact hc.trans (extensionBaseMap_triangle f u G hG M β).symm

private theorem extensionComponent_restriction_aux {T V V' : Scheme.{u}}
    (f : V' ⟶ V) (u : V ⟶ T) (v : V' ⟶ T) [Etale u] [Etale v]
    (h : f ≫ u = v)
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (M : T.Modules) (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) :
    let g : Scheme.Etale.mk v ⟶ Scheme.Etale.mk u := MorphismProperty.Over.homMk f h
    etaleTensorSectionsRestriction M g ≫
        extensionComponent M G hG β (Scheme.Etale.mk v) =
      extensionComponent M G hG β (Scheme.Etale.mk u) ≫ G.presheaf.map g.op := by
  subst v
  let g : Scheme.Etale.mk (f ≫ u) ⟶ Scheme.Etale.mk u :=
    MorphismProperty.Over.homMk f rfl
  let Nu := tensorExtensionZariskiRestriction u G hG
  let Nv := tensorExtensionZariskiRestriction (f ≫ u) G hG
  let au := ((extensionAdj u).homEquiv M Nu).symm
    (extensionBaseMap u G hG M β)
  let av := ((extensionAdj (f ≫ u)).homEquiv M Nv).symm
    (extensionBaseMap (f ≫ u) G hG M β)
  have ht := congrArg (fun a ↦ a.app ⊤) (extensionTranspose_triangle f u G hG M β)
  rw [Adjunction.homEquiv_unit] at ht
  change ((extensionAdj f).unit.app
      ((tensorPullback u).obj M)).app ⊤ ≫
        ((tensorSectionsComp f u).hom.app M).app ⊤ ≫ av.app ⊤ =
      au.app ⊤ ≫ (extensionTriangleMap f u (f ≫ u) rfl G hG).app ⊤ at ht
  have hunit : tensorSectionsUnit f ((tensorPullback u).obj M) =
      ((extensionAdj f).unit.app
        ((tensorPullback u).obj M)).app ⊤ := by
    have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : V'.Opens)) := rfl
    unfold tensorSectionsUnit
    erw [hi, ((tensorPullback f).obj ((tensorPullback u).obj M)).presheaf.map_id,
      Category.comp_id]
    rfl
  have hg : (tensorExtensionTopIso (f ≫ u)).inv ≫
        extensionTriangleArrow f u (f ≫ u) rfl ⊤ =
      g ≫ (tensorExtensionTopIso u).inv := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 V' ≫ V'.topIso.inv) ≫ (f ∣_ ⊤) = f ≫ (𝟙 V ≫ V.topIso.inv)
    simp only [Category.id_comp]
    apply (cancel_mono V.topIso.hom).mp
    rw [Category.assoc, show (f ∣_ ⊤) ≫ V.topIso.hom = V'.topIso.hom ≫ f
      from morphismRestrict_ι f ⊤]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only
  unfold etaleTensorSectionsRestriction
  simp only [eqToHom_refl, Hom.id_app]
  unfold extensionComponent
  change (tensorSectionsUnit f ((tensorPullback u).obj M) ≫
      ((tensorSectionsComp f u).hom.app M).app ⊤ ≫ av.app ⊤) ≫
        G.presheaf.map (tensorExtensionTopIso (f ≫ u)).inv.op =
      (au.app ⊤ ≫ G.presheaf.map (tensorExtensionTopIso u).inv.op) ≫ G.presheaf.map g.op
  rw [hunit, ht]
  simp only [Category.assoc]
  congr 1
  change G.presheaf.map (extensionTriangleArrow f u (f ≫ u) rfl ⊤).op ≫
      G.presheaf.map (tensorExtensionTopIso (f ≫ u)).inv.op = _
  rw [← G.presheaf.map_comp, ← G.presheaf.map_comp, ← op_comp, ← op_comp, hg]

private theorem extensionComponent_restriction {T : Scheme.{u}} (M : T.Modules)
    (G : _root_.PresheafOfModules.{u}
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG)
    {U V : T.Etale} (g : V ⟶ U) :
    etaleTensorSectionsRestriction M g ≫ extensionComponent M G hG β V =
      extensionComponent M G hG β U ≫ G.presheaf.map g.op := by
  exact extensionComponent_restriction_aux g.left U.hom V.hom g.w G hG M β

/-- The adjunction construction extends every Zariski module map, with the prescribed
components, open normalization and naturality in both modules. A sheaf G is presented
by its module presheaf and its sheaf-condition proof, exactly the data of SheafOfModules.
Linearity of every component together with the natural-transformation type says that
Theta is a morphism of module presheaves; no quasi-coherence is assumed.

Source: Stacks Project, Descent, Tag 070S (2), omitted small-site proof, using Sheaves,
Tag 0096 (blueprint: lem-trf-etale-tensor-sections-adjunction-extension).
Proof (the five steps of the DAG):
1. Restrict G to opens of each etale V. Open covers are etale covers, so these are
   Zariski modules. The sectionwise formula for b commutes with restrictions by
   functoriality of G and beta, and is semilinear for the direct-image scalar action.
   The tensor-pullback adjunction transposes b to a, a module map, and hence its
   global-sections map is linear.
2. For g : V' to V over T, restriction gives d_g : G_V to g_*G_V'. On every base
   open W, functoriality of G gives u_*d_g composed with b_u equal to b_v.
3. Compare g_*(a_v composed with c) composed with the g-unit and d_g composed
   with a_u. Their transposes under the u-adjunction are b_v: for the first use
   the composition-unit normalization of lem-sc-etale-qcoherent-presheaf-functorial;
   for the second use step 2. Injectivity of the Hom bijection of
   lem-pc-module-pullback-adjunction proves equality. Global sections give precisely
   the naturality square for the tensor-section restrictions.
4. On an open W the restriction-to-tensor comparison sends m to the i_W-unit
   applied to m, by lem-weil-pbc-open-immersion-module-pullback-restriction. The
   adjunction equation sends this to b_{i_W,W}(m), which is beta_W(m), since the
   remaining restriction is the identity. tensorOpenSectionIso is its inverse on
   sections, including the canonical identification of functions on the open.
5. For h and k, naturality of k gives b(k_T beta h) = u_*k_u composed with b(beta)
   composed with h. Naturality of the adjunction in both modules gives the same
   identity for a after pullback of h. Take global sections. The maps P_h commute
   with restrictions by lem-sc-etale-tensor-sections-map-naturality. Empty schemes,
   empty opens, identity arrows and zero modules use the same equations. -/
theorem etaleTensorSectionsAdjunctionExtension (T : Scheme.{u}) :
    ∃ Θ : ∀ (M : T.Modules)
        (G : _root_.PresheafOfModules.{u}
          (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
        (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf),
        (M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) →
          (etaleTensorSectionsPresheaf M ⟶ G.presheaf),
      (∀ (M : T.Modules)
          (G : _root_.PresheafOfModules.{u}
            (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
          (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
          (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG),
        (∀ U : T.Etale,
          ∃ b : M ⟶ (pushforward U.hom).obj
              (tensorExtensionZariskiRestriction U.hom G hG),
            (∀ (W : T.Opens) (m : Γ(M, W)),
              b.app W m = G.presheaf.map (tensorExtensionBaseChangeArrow U.hom W).op
                (β.app W m)) ∧
            (∀ s : Γ((tensorPullback U.hom).obj M, ⊤),
              (Θ M G hG β).app (op U) s =
                G.presheaf.map (tensorExtensionTopIso U.hom).inv.op
                  ((((Classical.choose (exists_tensorPullbackAdjunction U.hom)).homEquiv
                    M (tensorExtensionZariskiRestriction U.hom G hG)).symm b).app ⊤ s))) ∧
        (∀ (U : T.Etale) (r : Γ(U.left, ⊤))
            (s : Γ((tensorPullback U.hom).obj M, ⊤)),
          (Θ M G hG β).app (op U) ((((tensorPullback U.hom).obj M).smul r).hom s) =
            @SMul.smul
              ((T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
              (G.obj (op U)) inferInstance r ((Θ M G hG β).app (op U) s)) ∧
        (∀ (W : T.Opens) (m : Γ(M, W)),
          (Θ M G hG β).app (op (Scheme.Etale.mk W.ι))
              ((tensorOpenSectionIso T M W).inv m) =
            G.presheaf.map (tensorExtensionBaseOpenIso T W).inv.op (β.app W m))) ∧
      (∀ (M' M : T.Modules)
          (G G' : _root_.PresheafOfModules.{u}
            (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
          (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
          (hG' : Presheaf.IsSheaf T.smallEtaleTopology G'.presheaf)
          (β : M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG)
          (h : M' ⟶ M) (k : G ⟶ G') (U : T.Etale)
          (s : Γ((tensorPullback U.hom).obj M', ⊤)),
        (Θ M' G' hG' (h ≫ β ≫ tensorExtensionZariskiMap (𝟙 T) hG hG' k)).app (op U) s =
          k.app (op U) ((Θ M G hG β).app (op U) (((tensorPullback U.hom).map h).app ⊤ s))) := by
  let Θ : ∀ (M : T.Modules)
      (G : _root_.PresheafOfModules.{u}
        (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
      (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf),
      (M ⟶ tensorExtensionZariskiRestriction (𝟙 T) G hG) →
        (etaleTensorSectionsPresheaf M ⟶ G.presheaf) :=
    fun M G hG β ↦
      { app := fun U ↦ extensionComponent M G hG β U.unop
        naturality := fun U V g ↦ extensionComponent_restriction M G hG β g.unop }
  refine ⟨Θ, ?_, ?_⟩
  · intro M G hG β
    refine ⟨?_, ?_, ?_⟩
    · intro U
      refine ⟨extensionBaseMap U.hom G hG M β, ?_, ?_⟩
      · intro W m
        rfl
      · intro s
        rfl
    · intro U r s
      exact extensionComponent_smul M G hG β U r s
    · intro W m
      exact extensionComponent_open M G hG β W m
  · intro M' M G G' hG hG' β h k U s
    exact ConcreteCategory.congr_hom
      (extensionComponent_naturality M' M G G' hG hG' β h k U) s

end

end AlgebraicGeometry.Scheme.Modules
