/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Sites.Continuous
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Sheaf.Paper.CoefficientRingedSequenceSite
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso

/-! # Evaluation mates on vertical sequence sites

Source: Zheng, Construction 4.1; Stacks 0941 and 03D3.
(blueprint: lem-trf-vertical-evaluation-inverse-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe c v d w r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace CategoryTheory.VerticalEvaluation
variable {C : Type c} [Category.{v} C]
local instance sliceContinuous {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) :=
  WeilConjectures.sequenceInclusion_continuous J n
variable (A : (ℕ × C)ᵒᵖ ⥤ RingCat.{max r c v}) (n : ℕ)
private abbrev hor (V : (ℕ × C)ᵒᵖ) (h : n ≤ V.unop.1) :
    V ⟶ op (n, V.unop.2) := (Prod.mkHom (homOfLE h) (𝟙 V.unop.2)).op
private abbrev coValue (M : PresheafOfModules.{max r c v} ((Prod.sectR n C).op ⋙ A))
    (V : (ℕ × C)ᵒᵖ) : ModuleCat.{max r c v} (A.obj V) :=
  ModuleCat.of (A.obj V)
    (∀ h : PLift (n ≤ V.unop.1),
      (ModuleCat.restrictScalars (A.map (hor n V h.down)).hom).obj (M.obj (op V.unop.2)))
private abbrev coObj (M : PresheafOfModules.{max r c v} ((Prod.sectR n C).op ⋙ A)) :
    PresheafOfModules.{max r c v} A where
  obj := coValue.{c, v, r} A n M
  map {V W} a := ModuleCat.ofHom (X := coValue.{c, v, r} A n M V)
    (Y := (ModuleCat.restrictScalars (A.map a).hom).obj (coValue.{c, v, r} A n M W))
    { toFun := fun x h ↦ M.map a.unop.2.op (x ⟨h.down.trans (leOfHom a.unop.1)⟩)
      map_add' := by intros; funext h; exact map_add _ _ _
      map_smul' := by
        intro r x
        funext h
        change M.map a.unop.2.op
          ((A.map (hor n V (h.down.trans (leOfHom a.unop.1)))) r • x _) =
          (A.map (hor n W h.down)) ((A.map a) r) • M.map a.unop.2.op (x _)
        rw [M.map_smul]
        congr 1
        change (A.map (hor n V _) ≫ A.map ((Prod.sectR n C).map a.unop.2).op) r =
          (A.map a ≫ A.map (hor n W h.down)) r
        rw [← A.map_comp, ← A.map_comp]
        congr 2
        apply congrArg A.map
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext
        · apply Subsingleton.elim
        · simp [hor] }
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.map (𝟙 V.unop.2).op (x _) = x h
    rw [op_id, M.map_id]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.map (b.unop.2 ≫ a.unop.2).op (x _) =
      M.map b.unop.2.op (M.map a.unop.2.op (x _))
    rw [op_comp, M.map_comp_apply]


private abbrev coSheaf (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J)
      RingCat.{max r c v}) (n : ℕ)
    (M : SheafOfModules.{max r c v}
      (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
        (coefficientSequenceTopology J)).obj A)) :
    SheafOfModules.{max r c v} A where
  val := coObj.{c, v, r} A.obj n M.val
  isSheaf := by
    apply (Presheaf.isSheaf_iff_isSheaf_comp (coefficientSequenceTopology J)
      ((coObj.{c, v, r} A.obj n M.val).presheaf)
      (forget AddCommGrpCat.{max r c v})).mpr
    rw [isSheaf_iff_isSheaf_of_type]
    apply WeilConjectures.sequence_isSheaf_of_slices
    intro m U S hS x hx
    have hM : Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{max r c v}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        ((Presheaf.isSheaf_iff_isSheaf_comp J _
          (forget.{max r c v} AddCommGrpCat.{max r c v})).mp M.isSheaf)
    have hh (h : PLift (n ≤ m)) := hM S hS
      (fun {V} f hf ↦ x f hf h)
      (by
        intro V W Z a b f g hf hg hab
        exact congrFun (hx a b hf hg hab) h)
    choose a ha hu using hh
    refine ⟨fun h ↦ a h, ?_, ?_⟩
    · intro V f hf
      funext h
      exact ha h f hf
    · intro b hb
      funext h
      apply hu h (b h)
      intro V f hf
      exact congrFun (hb f hf) h


private abbrev coFunctor (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v}) (n : ℕ) :
    SheafOfModules.{max r c v}
      (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
        (coefficientSequenceTopology J)).obj A) ⥤ SheafOfModules.{max r c v} A where
  obj := coSheaf.{c, v, r} J A n
  map {M N} f :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := coValue.{c, v, r} A.obj n M.val V)
          (Y := coValue.{c, v, r} A.obj n N.val V)
          { toFun := fun x h ↦ f.val.app (op V.unop.2) (x h)
            map_add' := by intros; funext h; exact map_add _ _ _
            map_smul' := by intros; funext h; exact map_smul _ _ _ }
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          exact PresheafOfModules.naturality_apply f.val a.unop.2.op (x _) } }

private abbrev ev₀ (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v}) (n : ℕ) :=
  SheafOfModules.pushforward.{max r c v} (F := Prod.sectR n C)
    (𝟙 (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
      (coefficientSequenceTopology J)).obj A))

private abbrev coUnit (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v}) (n : ℕ) :
    𝟭 (SheafOfModules.{max r c v} A) ⟶ ev₀.{c, v, r} J A n ⋙ coFunctor.{c, v, r} J A n where
  app N :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom (X := N.val.obj V)
          (Y := coValue.{c, v, r} A.obj n ((ev₀.{c, v, r} J A n).obj N).val V)
          { toFun := fun x h ↦ N.val.map (hor n V h.down) x
            map_add' := by intros; funext h; exact map_add _ _ _
            map_smul' := by intros; funext h; exact N.val.map_smul _ _ _ }
        naturality := by
          intro V W a
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          change N.val.map (hor n W h.down) (N.val.map a x) =
            N.val.map ((Prod.sectR n C).map a.unop.2).op (N.val.map (hor n V _) x)
          refine (N.val.map_comp_apply a (hor n W h.down) x).symm.trans
            ((N.val.congr_map_apply
              (f := a ≫ hor n W h.down)
              (g := hor n V (h.down.trans (leOfHom a.unop.1)) ≫
                ((Prod.sectR n C).map a.unop.2).op) ?_ x).trans
              (N.val.map_comp_apply (hor n V (h.down.trans (leOfHom a.unop.1)))
                ((Prod.sectR n C).map a.unop.2).op x))
          apply Quiver.Hom.unop_inj
          apply Prod.hom_ext
          · apply Subsingleton.elim
          · simp [hor] } }
  naturality {M N} f := by
    ext V x
    funext h
    exact (PresheafOfModules.naturality_apply f.val (hor n V h.down) x).symm

private abbrev coCounit (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v}) (n : ℕ) :
    coFunctor.{c, v, r} J A n ⋙ ev₀.{c, v, r} J A n ⟶ 𝟭 _ where
  app M :=
    { val :=
      { app := fun V ↦ ModuleCat.ofHom
          (X := ((ev₀.{c, v, r} J A n).obj ((coFunctor.{c, v, r} J A n).obj M)).val.obj V)
          (Y := M.val.obj V)
          { toFun := fun x ↦ x ⟨le_refl n⟩
            map_add' := by intros; rfl
            map_smul' := by
              intro r x
              have hs : (r • x) ⟨le_refl n⟩ =
                  (A.obj.map (hor n (op (n, V.unop)) (le_refl n))) r •
                    (show M.val.obj V from x ⟨le_refl n⟩) := by
                rfl
              rw [hs]
              have h : hor n (op (n, V.unop)) (le_refl n) = 𝟙 _ := by
                apply Quiver.Hom.unop_inj
                apply Prod.hom_ext
                · apply Subsingleton.elim
                · rfl
              rw [h, A.obj.map_id]
              rfl }
        naturality := by intros; rfl } }
  naturality := by intros; rfl

private abbrev coAdj (J : GrothendieckTopology C)
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v}) (n : ℕ) :
    ev₀.{c, v, r} J A n ⊣ coFunctor.{c, v, r} J A n where
  unit := coUnit.{c, v, r} J A n
  counit := coCounit.{c, v, r} J A n
  left_triangle_components N := by
    ext V x
    change N.val.map (hor n (op (n, V.unop)) (le_refl n)) x = x
    have h : hor n (op (n, V.unop)) (le_refl n) = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      apply Prod.hom_ext
      · apply Subsingleton.elim
      · rfl
    rw [h, N.val.map_id]
    rfl
  right_triangle_components M := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    change M.val.map (𝟙 V.unop.2).op (x _) = x h
    rw [op_id, M.val.map_id]
    rfl

private theorem coMate_isIso
    {D : Type c} [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{max r c v}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{max r c v}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
        (coefficientSequenceTopology J)).obj A ⟶
      (F.sheafPushforwardContinuous RingCat.{max r c v} J K).obj
        (((Prod.sectR n D).sheafPushforwardContinuous RingCat.{max r c v} K
          (coefficientSequenceTopology K)).obj B))
    (d : SheafOfModules.pushforward.{max r c v} φ ⋙ ev₀.{c, v, r} J A n ≅
      ev₀.{c, v, r} K B n ⋙ SheafOfModules.pushforward.{max r c v} ψ)
    (hd : ∀ (N : SheafOfModules.{max r c v} B) (U : C)
        (x : ((SheafOfModules.pushforward.{max r c v} φ).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op U) x = x) :
    IsIso (mateEquiv (coAdj.{c, v, r} K B n) (coAdj.{c, v, r} J A n) d.hom) := by
  let β : coFunctor.{c, v, r} K B n ⋙ SheafOfModules.pushforward.{max r c v} φ ⟶
      SheafOfModules.pushforward.{max r c v} ψ ⋙ coFunctor.{c, v, r} J A n :=
    (mateEquiv (coAdj.{c, v, r} K B n) (coAdj.{c, v, r} J A n) d.hom).natTrans
  have hb (M) (V : (ℕ × C)ᵒᵖ)
      (x : ((coFunctor.{c, v, r} K B n ⋙ SheafOfModules.pushforward.{max r c v} φ).obj M).val.obj V)
      (h : PLift (n ≤ V.unop.1)) :
      ((β.app M).val.app V x) h = x h := by
    change (((SheafOfModules.pushforward.{max r c v} ψ).map ((coAdj.{c, v, r} K B n).counit.app
      M)).val.app
      (op V.unop.2)
      ((d.hom.app ((coFunctor.{c, v, r} K B n).obj M)).val.app (op V.unop.2)
        (((SheafOfModules.pushforward.{max r c v} φ).obj ((coFunctor.{c, v, r} K B n).obj
          M)).val.map
          (hor n V h.down) x))) = x h
    rw [hd]
    change M.val.map (F.map (𝟙 V.unop.2)).op (x _) = x h
    rw [F.map_id, op_id, M.val.map_id]
    rfl
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro M
  let T := SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj
  have ht : IsIso (T.map (β.app M)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hf : (fun x ↦ (T.map (β.app M)).app V x) = fun x ↦ x := by
      funext x
      funext h
      exact hb M V x h
    constructor
    · intro x y hxy
      have hx := congrFun hf x
      have hy := congrFun hf y
      exact hx.symm.trans (hxy.trans hy)
    · intro y
      exact ⟨y, congrFun hf y⟩
  let := ht
  exact isIso_of_reflects_iso (β.app M) T

/-- The inverse geometric mate of the sectionwise evaluation square is invertible.
No equality between site and coefficient universes is required.
Source: Zheng 4.1; Stacks 0941 and 03D3
(blueprint: lem-trf-vertical-evaluation-inverse-mate).

Proof: right coextension of a level module has sections indexed by proofs of n≤m
at (m,U), with the action restricted along the horizontal ring map. Thus its section
module is the given module for m≥n and zero for m<n. Horizontal restriction is the
unit and evaluation at the reflexive inequality is the counit. Under these explicit
adjunctions the evaluation square has a mate equal to the identity on every section,
hence invertible. The iterated-mates identity identifies its conjugate with the
inverse geometric mate, and conjugation preserves isomorphisms. -/
theorem inverseMate_isIso
    {D : Type c} [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{max r c v}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{max r c v}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
        (coefficientSequenceTopology J)).obj A ⟶
      (F.sheafPushforwardContinuous RingCat.{max r c v} J K).obj
        (((Prod.sectR n D).sheafPushforwardContinuous RingCat.{max r c v} K
          (coefficientSequenceTopology K)).obj B))
    (L : SheafOfModules.{max r c v} A ⥤ SheafOfModules.{max r c v} B)
    (adj : L ⊣ SheafOfModules.pushforward.{max r c v} φ)
    (Ln : SheafOfModules.{max r c v}
        (((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
          (coefficientSequenceTopology J)).obj A) ⥤ SheafOfModules.{max r c v}
        (((Prod.sectR n D).sheafPushforwardContinuous RingCat.{max r c v} K
          (coefficientSequenceTopology K)).obj B))
    (adjn : Ln ⊣ SheafOfModules.pushforward.{max r c v} ψ)
    (e : SheafOfModules.pushforward.{max r c v} φ ⋙
        SheafOfModules.pushforward.{max r c v} (F := Prod.sectR n C) (𝟙 _) ≅
      SheafOfModules.pushforward.{max r c v} (F := Prod.sectR n D) (𝟙 _) ⋙
        SheafOfModules.pushforward.{max r c v} ψ)
    (he : ∀ (N : SheafOfModules.{max r c v} B) (U : C)
        (x : ((SheafOfModules.pushforward.{max r c v} φ).obj N).val.obj (op (n, U))),
      (e.hom.app N).val.app (op U) x = x) :
    IsIso ((mateEquiv adj adjn).symm e.hom).natTrans := by
  have hi := coMate_isIso.{c, v, r} J K F A B n φ ψ e he
  let α := ((mateEquiv adj adjn).symm e.hom).natTrans
  have h := iterated_mateEquiv_conjugateEquiv adj adjn (coAdj.{c, v, r} J A n) (coAdj.{c, v, r} K
    B n) α
  change ((mateEquiv (coAdj.{c, v, r} K B n) (coAdj.{c, v, r} J A n))
    ((mateEquiv adj adjn) ((mateEquiv adj adjn).symm e.hom))).natTrans = _ at h
  rw [Equiv.apply_symm_apply] at h
  have : IsIso (conjugateEquiv (adj.comp (coAdj.{c, v, r} K B n))
      ((coAdj.{c, v, r} J A n).comp adjn) α) := by
    rw [← h]
    exact hi
  exact conjugateEquiv_of_iso (adj.comp (coAdj.{c, v, r} K B n)) ((coAdj.{c, v, r} J A n).comp
    adjn) α

/-- A vertical evaluation commutes with module direct image when its ring square commutes.
Source: Stacks 0941 (blueprint: lem-trf-vertical-evaluation-inverse-mate).
Proof: compose continuous module pushforwards on each side and identify their
structural maps by the given square. Both comparisons are the identity on sections. -/
theorem pushforwardEvaluation
    {D : Type c} [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{max r c v}) (n : ℕ)
    (S : Sheaf J RingCat.{max r c v}) (T : Sheaf K RingCat.{max r c v})
    (a : S ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v}
      J (coefficientSequenceTopology J)).obj A)
    (b : T ⟶ ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{max r c v}
      K (coefficientSequenceTopology K)).obj B)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{max r c v}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{max r c v} J K).obj T)
    (h : ∀ U : Cᵒᵖ, a.hom.app U ≫ φ.hom.app (op (n, U.unop)) =
      ψ.hom.app U ≫ b.hom.app (F.op.obj U)) :
    ∃ e : SheafOfModules.pushforward.{max r c v} φ ⋙ SheafOfModules.pushforward a ≅
        SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ,
      ∀ (N : SheafOfModules.{max r c v} B) (U : C)
        (x : ((SheafOfModules.pushforward φ).obj N).val.obj (op (n, U))),
        (e.hom.app N).val.app (op U) x = x := by
  have := Functor.isContinuous_comp (Prod.sectR n C) ((𝟭 ℕ).prod F)
    J (coefficientSequenceTopology J) (coefficientSequenceTopology K)
  have := Functor.isContinuous_comp F (Prod.sectR n D)
    J K (coefficientSequenceTopology K)
  have he : a ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v}
      J (coefficientSequenceTopology J)).map φ =
      ψ ≫ (F.sheafPushforwardContinuous RingCat.{max r c v} J K).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact h U
  let e : SheafOfModules.pushforward.{max r c v} φ ⋙ SheafOfModules.pushforward a ≅
      SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ :=
    SheafOfModules.pushforwardComp a φ ≪≫ SheafOfModules.pushforwardCongr he ≪≫
      (SheafOfModules.pushforwardComp ψ b).symm
  exact ⟨e, fun _ _ _ ↦ rfl⟩

/-- Transport of the evaluation-mate theorem along prescribed ring identifications.
Source: Zheng 4.1 (blueprint: lem-trf-vertical-evaluation-inverse-mate).
Proof: substitute the two ring equalities and apply the sectionwise theorem. -/
theorem inverseMateFor_isIso
    {D : Type c} [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)]
    (A : Sheaf (coefficientSequenceTopology J) RingCat.{max r c v})
    (B : Sheaf (coefficientSequenceTopology K) RingCat.{max r c v}) (n : ℕ)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{max r c v}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (S : Sheaf J RingCat.{max r c v}) (T : Sheaf K RingCat.{max r c v})
    (hS : ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{max r c v} J
      (coefficientSequenceTopology J)).obj A = S)
    (hT : ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{max r c v} K
      (coefficientSequenceTopology K)).obj B = T)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{max r c v} J K).obj T)
    (L : SheafOfModules.{max r c v} A ⥤ SheafOfModules.{max r c v} B)
    (adj : L ⊣ SheafOfModules.pushforward.{max r c v} φ)
    (Ln : SheafOfModules.{max r c v} S ⥤ SheafOfModules.{max r c v} T)
    (adjn : Ln ⊣ SheafOfModules.pushforward.{max r c v} ψ)
    (e : SheafOfModules.pushforward.{max r c v} φ ⋙
        SheafOfModules.pushforward.{max r c v} (F := Prod.sectR n C) (eqToHom hS.symm) ≅
      SheafOfModules.pushforward.{max r c v} (F := Prod.sectR n D) (eqToHom hT.symm) ⋙
        SheafOfModules.pushforward.{max r c v} ψ)
    (he : ∀ (N : SheafOfModules.{max r c v} B) (U : C)
        (x : ((SheafOfModules.pushforward.{max r c v} φ).obj N).val.obj (op (n, U))),
      (e.hom.app N).val.app (op U) x = x) :
    IsIso ((mateEquiv adj adjn).symm e.hom).natTrans := by
  subst S
  subst T
  exact inverseMate_isIso.{c, v, r} J K F A B n φ ψ L adj Ln adjn e he

end CategoryTheory.VerticalEvaluation
