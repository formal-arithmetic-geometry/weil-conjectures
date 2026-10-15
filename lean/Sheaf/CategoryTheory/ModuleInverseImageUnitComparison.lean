/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.SheafPullbackUnitPresentation
import Sheaf.CategoryTheory.ModuleInverseImageAction
import all Sheaf.CategoryTheory.ModuleInverseImageAdjunction
import all Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction

/-! Unit compatibility for module inverse-image comparisons. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj B)
open MonoidalCategory
variable (hgen : ∀ (M : SheafOfModules.{u} A) (T : Sheaf K (Type u))
  (a b : (sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B ⊗
    (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M)) ⟶ T),
  (∀ (U : Cᵒᵖ) (r : A.obj.obj U) (m : M.val.obj U),
    a.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m) =
      b.hom.app (F.op.obj U)
        (φ.hom.app U r,
          ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M)).hom.app U m)) → a = b)
include hgen in
private theorem inverseImage_underlying_unit_of_actions
    (actions : ∀ M : SheafOfModules.{u} A, InverseImageAction φ M) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
        toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M, (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
          (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
            ((toSheaf A).obj M) := by
  let La := sheafPullback F AddCommGrpCat.{u} J K
  let Ra := F.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  let adj := sheafAdjunctionContinuous F AddCommGrpCat.{u} J K
  let P := toSheaf A
  let Q := toSheaf B
  let T := pushforward.{u} φ
  let obj (M : SheafOfModules.{u} A) := (actions M).toModule
  let lift (M : SheafOfModules.{u} A) (N : SheafOfModules.{u} B)
      (α : La.obj (P.obj M) ⟶ Q.obj N)
      (hβ : ∀ U (r : A.obj.obj U) (m : M.val.obj U),
        (adj.homEquiv _ _ α).hom.app U (r • m) =
          @SMul.smul (B.obj.obj (F.op.obj U)) (N.val.obj (F.op.obj U)) inferInstance
            (φ.hom.app U r) ((adj.homEquiv _ _ α).hom.app U m)) : obj M ⟶ N :=
    ⟨PresheafOfModules.homMk α.hom
      (linear_of_adjunct_linear φ hgen M N (actions M) α hβ)⟩
  let η (M : SheafOfModules.{u} A) : M ⟶ T.obj (obj M) :=
    ⟨PresheafOfModules.homMk (adj.unit.app (P.obj M)).hom
      (fun U r m ↦ (actions M).unit_smul U r m)⟩
  let map {M N : SheafOfModules.{u} A} (g : M ⟶ N) : obj M ⟶ obj N :=
    lift M (obj N) (La.map (P.map g)) (by
      intro U r m
      change (adj.homEquiv (P.obj M) (La.obj (P.obj N))
        (La.map (P.map g))).hom.app U (r • m) =
        @SMul.smul (B.obj.obj (F.op.obj U)) ((obj N).val.obj (F.op.obj U)) inferInstance
          (φ.hom.app U r) ((adj.homEquiv (P.obj M) (La.obj (P.obj N))
            (La.map (P.map g))).hom.app U m)
      have h : adj.homEquiv _ _ (La.map (P.map g)) =
          P.map g ≫ adj.unit.app (P.obj N) := by
        rw [Adjunction.homEquiv_unit, adj.unit_naturality]
      rw [h]
      change (η N).val.app U (g.val.app U (r • m)) = _
      rw [(g.val.app U).hom.map_smul]
      exact ((η N).val.app U).hom.map_smul r (g.val.app U m))
  have hmap₀ {M N : SheafOfModules.{u} A} (g : M ⟶ N) :
      Q.map (map g) = La.map (P.map g) := by
    ext U m
    rfl
  let L : SheafOfModules.{u} A ⥤ SheafOfModules.{u} B :=
    { obj := obj
      map := map
      map_id := by
        intro M
        apply Q.map_injective
        rw [hmap₀, P.map_id, La.map_id, Q.map_id]
        rfl
      map_comp := by
        intro M N O g h
        apply Q.map_injective
        rw [Q.map_comp, hmap₀, hmap₀, hmap₀]
        exact (P ⋙ La).map_comp g h }
  have hmap {M N : SheafOfModules.{u} A} (g : M ⟶ N) :
      Q.map (L.map g) = La.map (P.map g) := hmap₀ g
  let e : L ⋙ Q ≅ P ⋙ La := NatIso.ofComponents
    (fun M ↦ (actions M).underlyingIso) (by
      intro M N g
      change Q.map (L.map g) ≫ 𝟙 _ = 𝟙 _ ≫ La.map (P.map g)
      simpa using hmap g)
  let d : T ⋙ P ≅ Q ⋙ Ra := Iso.refl _
  have hlin (M : SheafOfModules.{u} A) (N : SheafOfModules.{u} B)
      (α : La.obj (P.obj M) ⟶ Q.obj N) :
      (∃ h : L.obj M ⟶ N, Q.map h = e.hom.app M ≫ α) ↔
        ∃ k : M ⟶ T.obj N,
          P.map k ≫ d.hom.app N = adj.homEquiv _ _ α := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨η M ≫ T.map h, ?_⟩
      change adj.unit.app (P.obj M) ≫ Ra.map (Q.map h) ≫ 𝟙 _ = _
      change Q.map h = 𝟙 _ ≫ α at hh
      simp only [Category.id_comp] at hh
      rw [hh, Category.comp_id]
      rfl
    · rintro ⟨k, hk⟩
      have hk' : P.map k = adj.homEquiv _ _ α := by
        change P.map k ≫ 𝟙 _ = _ at hk
        simpa only [Category.comp_id] using hk
      refine ⟨lift M N α (fun U r m ↦ ?_), ?_⟩
      · rw [← hk']
        exact (k.val.app U).hom.map_smul r m
      · ext U m
        rfl
  obtain ⟨am, _, hu, _⟩ :=
    AlgebraicGeometry.adjunctionOfLinearLifts L T La Ra P Q adj e d hlin
  let q := (pullbackPushforwardAdjunction φ).leftAdjointUniq am
  refine ⟨Functor.isoWhiskerRight q Q ≪≫ e, ?_⟩
  intro M
  have hq := Adjunction.unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction φ) am M
  have h := congrArg P.map hq
  have hh : P.map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
      P.map (T.map (q.hom.app M)) = P.map (am.unit.app M) := by
    simpa only [Functor.map_comp] using h
  have hu0 : P.map (am.unit.app M) = adj.unit.app (P.obj M) := by
    have hu' := hu M
    change P.map (am.unit.app M) ≫ 𝟙 _ =
      adj.unit.app (P.obj M) ≫ Ra.map (𝟙 _) at hu'
    erw [Ra.map_id] at hu'
    exact (Category.comp_id _).symm.trans (hu'.trans (Category.comp_id _))
  change P.map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
    Ra.map (Q.map (q.hom.app M) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  change P.map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
    P.map (T.map (q.hom.app M)) = _
  exact hh.trans hu0



/-- The underlying module inverse image comparison respects the adjunction unit.
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: lem-weil-pbc-module-inverse-image-unit-comparison).
Proof: use the ring and abelian unit presentations to construct the scalar action
on the actual abelian inverse image. Unit generators detect linearity of adjoints.
The restricted adjunction therefore has the abelian unit as its underlying unit.
Uniqueness of left adjoints compares the chosen module pullback with this lift;
the unit equation for that comparison gives the asserted equation. -/
theorem inverseImage_underlying_unit_of_ring_presentation
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M, (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
        (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
          ((toSheaf A).obj M) := by
  let ea := sheafPullbackForgetIso J K F (CategoryTheory.forget AddCommGrpCat.{u})
  let pa (M : SheafOfModules.{u} A) : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj ((toSheaf A).obj M))
      ((sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((sheafPullback F AddCommGrpCat.{u} J K).obj ((toSheaf A).obj M))) :=
    { unit := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
        ((sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app ((toSheaf A).obj M))
      iso := ea.app ((toSheaf A).obj M)
      equation := fun U x ↦ by
        have h := sheafPullbackForgetIso_unit J K F
          (CategoryTheory.forget AddCommGrpCat.{u}) ((toSheaf A).obj M)
        exact congrArg (fun t ↦ t.hom.app U x) h }
  apply inverseImage_underlying_unit_of_actions φ
    (fun M Z a b h ↦ ?_) (fun M ↦ Classical.choice
      (inverseImageAction_of_presentations φ M pr hr (pa M) rfl))
  apply (pr.tensor (pa M)).hom_ext a b
  intro U x
  change a.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2) =
    b.hom.app (F.op.obj U) (pr.unit.hom.app U x.1, (pa M).unit.hom.app U x.2)
  rw [hr]
  exact h U x.1 x.2

end SheafOfModules
