/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable

/-! # The canonical set-sheaf comparison for localization of a site

Source: Stacks Project, Sites, Tag 03CF; Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-set-pullback-isIso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J] (V : D)
  [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]

/-- The direct-image square for set sheaves is identity on sections.
Source: Stacks Tag 03CF
(blueprint: lem-weil-pbc-slice-set-pullback-isIso). -/
def sliceSetPushforwardIso :
    u.sheafPushforwardContinuous (Type u) K J ⋙ K.overPullback (Type u) V ≅
      J.overPullback (Type u) (u.obj V) ⋙
        (Over.post (X := V) u).sheafPushforwardContinuous (Type u)
          (K.over V) (J.over (u.obj V)) :=
  NatIso.ofComponents (fun G ↦ ObjectProperty.isoMk _ (Iso.refl _))

/-- The set inverse-image comparison, defined as the inverse mate.
Source: Stacks Tags 03CF and 04J0
(blueprint: lem-weil-pbc-slice-set-pullback-isIso). -/
def sliceSetPullbackMap :
    K.overPullback (Type u) V ⋙
        (Over.post (X := V) u).sheafPullback (Type u)
          (K.over V) (J.over (u.obj V)) ⟶
      u.sheafPullback (Type u) K J ⋙
        J.overPullback (Type u) (u.obj V) :=
  ((mateEquiv (u.sheafAdjunctionContinuous (Type u) K J)
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
      (K.over V) (J.over (u.obj V)))).symm
        (TwoSquare.mk _ _ _ _ (sliceSetPushforwardIso (K := K) (J := J) u V).hom)).natTrans

/-- The unit equation characterizes the canonical set inverse mate.
Source: Stacks Tags 03CF and 04J0
(blueprint: lem-weil-pbc-slice-set-pullback-isIso). -/
theorem sliceSetPullbackMap_unit (R : Sheaf K (Type u)) :
    (K.overPullback (Type u) V).map
        ((u.sheafAdjunctionContinuous (Type u) K J).unit.app R) ≫
      (sliceSetPushforwardIso (K := K) (J := J) u V).hom.app
        ((u.sheafPullback (Type u) K J).obj R) =
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
        (K.over V) (J.over (u.obj V))).unit.app (R.over V) ≫
      ((Over.post (X := V) u).sheafPushforwardContinuous (Type u)
        (K.over V) (J.over (u.obj V))).map
          ((sliceSetPullbackMap (K := K) (J := J) u V).app R) := by
  exact unit_mateEquiv_symm
    (u.sheafAdjunctionContinuous (Type u) K J)
    ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
      (K.over V) (J.over (u.obj V)))
    (TwoSquare.mk _ _ _ _ (sliceSetPushforwardIso (K := K) (J := J) u V).hom) R

/-- A set comparison satisfying the canonical unit equation is the inverse mate.
Source: Stacks Tags 03CF and 04J0, uniqueness under the sheaf adjunction
(blueprint: lem-weil-pbc-slice-set-pullback-isIso). -/
theorem sliceSetPullbackMap_eq_of_unit
    (t : K.overPullback (Type u) V ⋙
        (Over.post (X := V) u).sheafPullback (Type u)
          (K.over V) (J.over (u.obj V)) ⟶
      u.sheafPullback (Type u) K J ⋙
        J.overPullback (Type u) (u.obj V))
    (ht : ∀ R : Sheaf K (Type u),
      ((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
        (K.over V) (J.over (u.obj V))).unit.app (R.over V) ≫
        ((Over.post (X := V) u).sheafPushforwardContinuous (Type u)
          (K.over V) (J.over (u.obj V))).map (t.app R) =
      (K.overPullback (Type u) V).map
          ((u.sheafAdjunctionContinuous (Type u) K J).unit.app R) ≫
        (sliceSetPushforwardIso (K := K) (J := J) u V).hom.app
          ((u.sheafPullback (Type u) K J).obj R)) :
    t = sliceSetPullbackMap (K := K) (J := J) u V := by
  apply NatTrans.ext
  funext R
  apply (((Over.post (X := V) u).sheafAdjunctionContinuous (Type u)
    (K.over V) (J.over (u.obj V))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ht]
  exact sliceSetPullbackMap_unit (K := K) (J := J) u V R

end CategoryTheory
namespace CategoryTheory
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  (eC : C ≌ E) (eD : D ≌ F)
  (b : R₁ ⋙ eC.functor ≅ eD.functor ⋙ R₂)

private theorem equivalentMate_bijective (A : C) (B : D) :
    Function.Bijective (fun g : eD.functor.obj (L₁.obj A) ⟶ eD.functor.obj B ↦
      ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A ≫ g) := by
  let l := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A
  let h := eD.fullyFaithfulFunctor.homEquiv.symm |>.trans (a₁.homEquiv A B)
  let k := h.trans eC.fullyFaithfulFunctor.homEquiv
  let z := k.trans (Iso.homCongr (Iso.refl _) (b.app B))
  have hz (g : eD.functor.obj (L₁.obj A) ⟶ eD.functor.obj B) :
      a₂.homEquiv _ _ (l ≫ g) = z g := by
    obtain ⟨g, rfl⟩ := eD.fullyFaithfulFunctor.homEquiv.surjective g
    rw [Adjunction.homEquiv_unit, R₂.map_comp, ← Category.assoc]
    change (a₂.unit.app (eC.functor.obj A) ≫
      R₂.map (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A)) ≫
        R₂.map (eD.functor.map g) = z (eD.functor.map g)
    have hu := unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ b.hom) A
    change eC.functor.map (a₁.unit.app A) ≫ b.hom.app (L₁.obj A) =
      a₂.unit.app (eC.functor.obj A) ≫ R₂.map
        (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A) at hu
    rw [← hu]
    have hn := b.hom.naturality g
    change eC.functor.map (R₁.map g) ≫ b.hom.app B =
      b.hom.app (L₁.obj A) ≫ R₂.map (eD.functor.map g) at hn
    rw [Category.assoc, ← hn, ← eC.functor.map_comp_assoc]
    simp [z, k, h, Adjunction.homEquiv_unit]
  rw [← (a₂.homEquiv _ _).bijective.of_comp_iff']
  change Function.Bijective (fun g ↦ a₂.homEquiv _ _ (l ≫ g))
  have he : (fun g ↦ a₂.homEquiv _ _ (l ≫ g)) = z := funext hz
  rw [he]
  exact z.bijective

private theorem equivalentMate_isIso :
    IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  apply isIso_of_coyoneda_map_bijective
  intro B
  let l := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app A
  let z := eD.counitIso.app B
  have h := equivalentMate_bijective a₁ a₂ eC eD b A (eD.inverse.obj B)
  constructor
  · intro g g' hh
    apply (cancel_mono z.inv).1
    apply h.injective
    change l ≫ g ≫ z.inv = l ≫ g' ≫ z.inv
    change l ≫ g = l ≫ g' at hh
    rw [← Category.assoc, ← Category.assoc, hh]
  · intro k
    obtain ⟨g, hg⟩ := h.surjective (k ≫ z.inv)
    refine ⟨g ≫ z.hom, ?_⟩
    change l ≫ g = k ≫ z.inv at hg
    change l ≫ g ≫ z.hom = k
    rw [← Category.assoc, hg, Category.assoc, z.inv_hom_id]
    exact Category.comp_id k
end CategoryTheory
namespace CategoryTheory
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  (K : GrothendieckTopology D) (J : GrothendieckTopology C)
  (f : D ⥤ C) [f.IsContinuous K J] (V : D)

private abbrev sy (K : GrothendieckTopology D) (V : D) : Sheaf K (Type u) :=
  (presheafToSheaf K (Type u)).obj (yoneda.obj V)

private def syEquiv (H : Sheaf K (Type u)) : (sy K V ⟶ H) ≃ H.obj.obj (op V) :=
  ((sheafificationAdjunction K (Type u)).homEquiv _ _).trans yonedaEquiv

private theorem syEquiv_comp (H H' : Sheaf K (Type u)) (a : sy K V ⟶ H) (b : H ⟶ H') :
    syEquiv K V H' (a ≫ b) = b.hom.app (op V) (syEquiv K V H a) := by
  dsimp only [syEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  exact yonedaEquiv_comp _ _

private def syPullbackMap : (f.sheafPullback (Type u) K J).obj (sy K V) ⟶ sy J (f.obj V) :=
  ((f.sheafAdjunctionContinuous (Type u) K J).homEquiv _ _).symm
    ((syEquiv K V _).symm (syEquiv J (f.obj V) _ (𝟙 _)))

private theorem syPullbackMap_isIso : IsIso (syPullbackMap K J f V) := by
  apply isIso_of_coyoneda_map_bijective
  intro H
  let e : ((f.sheafPullback (Type u) K J).obj (sy K V) ⟶ H) ≃
      H.obj.obj (op (f.obj V)) :=
    ((f.sheafAdjunctionContinuous (Type u) K J).homEquiv _ _).trans (syEquiv K V _)
  have he (a : sy J (f.obj V) ⟶ H) :
      e (syPullbackMap K J f V ≫ a) = syEquiv J (f.obj V) H a := by
    dsimp only [e, Equiv.trans_apply, syPullbackMap]
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have h := syEquiv_comp K V _ _
      ((syEquiv K V _).symm (syEquiv J (f.obj V) _ (𝟙 _)))
      ((f.sheafPushforwardContinuous (Type u) K J).map a)
    rw [Equiv.apply_symm_apply] at h
    exact h.trans (by
      change a.hom.app (op (f.obj V)) _ = _
      simpa using (syEquiv_comp J (f.obj V) _ H (𝟙 _) a).symm)
  have hh : (fun a : sy J (f.obj V) ⟶ H ↦ syPullbackMap K J f V ≫ a) =
      e.symm ∘ (syEquiv J (f.obj V) H) := by
    funext a
    exact e.injective ((he a).trans (e.apply_symm_apply _).symm)
  rw [hh]
  exact e.symm.bijective.comp (syEquiv J (f.obj V) H).bijective

private def syPushMap : sy K V ⟶ (f.sheafPushforwardContinuous (Type u) K J).obj
    (sy J (f.obj V)) :=
  (syEquiv K V _).symm (syEquiv J (f.obj V) _ (𝟙 _))

private theorem syPushMap_unit (T : D) (h : T ⟶ V) :
    (syPushMap K J f V).hom.app (op T) ((toSheafify K (yoneda.obj V)).app (op T) h) =
      (toSheafify J (yoneda.obj (f.obj V))).app (op (f.obj T)) (f.map h) := by
  have hh : toSheafify K (yoneda.obj V) ≫ (syPushMap K J f V).hom =
      (yonedaEquiv (X := V) (F :=
        ((f.sheafPushforwardContinuous (Type u) K J).obj (sy J (f.obj V))).obj)).symm
          (syEquiv J (f.obj V) _ (𝟙 _)) := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    change syEquiv K V _ (syPushMap K J f V) = _
    exact (syEquiv K V _).apply_symm_apply _
  have hcomp := congrArg (fun a ↦ a.app (op T) h) hh
  change _ = (sy J (f.obj V)).obj.map (f.map h).op
    (syEquiv J (f.obj V) _ (𝟙 _)) at hcomp
  have hn := (toSheafify J (yoneda.obj (f.obj V))).naturality_apply
    (f.map h).op (𝟙 (f.obj V))
  exact hcomp.trans (by
    change (sheafify J (yoneda.obj (f.obj V))).map (f.map h).op
      ((toSheafify J (yoneda.obj (f.obj V))).app (op (f.obj V)) (𝟙 _)) = _
    change _ = _ at hn
    have hn' :
        (toSheafify J (yoneda.obj (f.obj V))).app (op (f.obj T)) (f.map h ≫ 𝟙 _) =
          (sheafify J (yoneda.obj (f.obj V))).map (f.map h).op
            ((toSheafify J (yoneda.obj (f.obj V))).app (op (f.obj V)) (𝟙 _)) := hn
    rw [Category.comp_id] at hn'
    exact hn'.symm)

private def sliceLeftOver : Over (sy K V) ⥤ Over (sy J (f.obj V)) :=
  Over.post (f.sheafPullback (Type u) K J) ⋙ Over.map (syPullbackMap K J f V)

private def sliceRightOver : Over (sy J (f.obj V)) ⥤ Over (sy K V) :=
  Over.post (f.sheafPushforwardContinuous (Type u) K J) ⋙
    Over.pullback (syPushMap K J f V)

private def sliceOverAdjunction : sliceLeftOver K J f V ⊣ sliceRightOver K J f V := by
  let a := syPushMap K J f V
  let adj := f.sheafAdjunctionContinuous (Type u) K J
  let adj₀ := (Over.mapPullbackAdj a).comp (Over.postAdjunctionRight
    (Y := sy J (f.obj V)) adj)
  apply adj₀.ofNatIsoLeft
  exact NatIso.ofComponents (fun A ↦ Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (f.sheafPullback (Type u) K J).map A.hom ≫
        syPullbackMap K J f V =
      (f.sheafPullback (Type u) K J).map (A.hom ≫ a) ≫
        adj.counit.app (sy J (f.obj V))
    rw [Category.id_comp, Functor.map_comp, Category.assoc]
    rfl)) (by intro A B g; apply Over.OverMorphism.ext; rfl)

private def sectionsPullbackEquiv {X Y Z : Sheaf K (Type u)}
    (a : X ⟶ Z) (b : Y ⟶ Z) (T : D) :
    (pullback a b).obj.obj (op T) ≃
      {p : X.obj.obj (op T) × Y.obj.obj (op T) |
        a.hom.app (op T) p.1 = b.hom.app (op T) p.2} := by
  let ev := sheafToPresheaf K (Type u) ⋙ (evaluation Dᵒᵖ (Type u)).obj (op T)
  exact PullbackCone.IsLimit.equivPullbackObj
    (isLimitOfHasPullbackOfPreservesLimit ev a b)

@[simp] private theorem sectionsPullbackEquiv_fst {X Y Z : Sheaf K (Type u)}
    (a : X ⟶ Z) (b : Y ⟶ Z) (T : D) (s : (pullback a b).obj.obj (op T)) :
    (sectionsPullbackEquiv K a b T s).val.1 = (pullback.fst a b).hom.app (op T) s :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst _ _

@[simp] private theorem sectionsPullbackEquiv_snd {X Y Z : Sheaf K (Type u)}
    (a : X ⟶ Z) (b : Y ⟶ Z) (T : D) (s : (pullback a b).obj.obj (op T)) :
    (sectionsPullbackEquiv K a b T s).val.2 = (pullback.snd a b).hom.app (op T) s :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd _ _

@[simp] private theorem sectionsPullbackEquiv_inv_fst {X Y Z : Sheaf K (Type u)}
    (a : X ⟶ Z) (b : Y ⟶ Z) (T : D)
    (s : {p : X.obj.obj (op T) × Y.obj.obj (op T) |
      a.hom.app (op T) p.1 = b.hom.app (op T) p.2}) :
    (pullback.fst a b).hom.app (op T) ((sectionsPullbackEquiv K a b T).symm s) = s.val.1 := by
  obtain ⟨s, rfl⟩ := (sectionsPullbackEquiv K a b T).surjective s
  simp only [Equiv.symm_apply_apply, sectionsPullbackEquiv_fst]

@[simp] private theorem sectionsPullbackEquiv_inv_snd {X Y Z : Sheaf K (Type u)}
    (a : X ⟶ Z) (b : Y ⟶ Z) (T : D)
    (s : {p : X.obj.obj (op T) × Y.obj.obj (op T) |
      a.hom.app (op T) p.1 = b.hom.app (op T) p.2}) :
    (pullback.snd a b).hom.app (op T) ((sectionsPullbackEquiv K a b T).symm s) = s.val.2 := by
  obtain ⟨s, rfl⟩ := (sectionsPullbackEquiv K a b T).surjective s
  simp only [Equiv.symm_apply_apply, sectionsPullbackEquiv_snd]

private def pulledFibre {D C : Type u} [SmallCategory D] [SmallCategory C]
    (K : GrothendieckTopology D) (J : GrothendieckTopology C) (f : D ⥤ C)
    [f.IsContinuous K J] (V : D)
    (F : Over ((presheafToSheaf J (Type u)).obj (yoneda.obj (f.obj V)))) :
    Subfunctor (((f.sheafPushforwardContinuous (Type u) K J).obj F.left).over V).obj where
  obj X := {s | F.hom.hom.app (op (f.obj X.unop.left)) s =
    (toSheafify J (yoneda.obj (f.obj V))).app (op (f.obj X.unop.left))
      (f.map X.unop.hom)}
  map {X Y} b s hs := by
    change F.hom.hom.app _ (F.left.obj.map (f.map b.unop.left).op s) = _
    rw [NatTrans.naturality_apply, hs, ← NatTrans.naturality_apply]
    congr 1
    change f.map b.unop.left ≫ f.map X.unop.hom = f.map Y.unop.hom
    rw [← f.map_comp, Over.w]


private def sliceRightFibreEquiv (F : Over (sy J (f.obj V))) (T : Over V) :
    ((fibreFunctor K V).obj ((sliceRightOver K J f V).obj F)).obj.obj (op T) ≃
      (pulledFibre K J f V F).obj (op T) where
  toFun s := ⟨(pullback.fst
      ((f.sheafPushforwardContinuous (Type u) K J).map F.hom)
      (syPushMap K J f V)).hom.app (op T.left) s.val, by
    have hp := congrArg (fun a ↦ a.hom.app (op T.left) s.val)
      (pullback.condition (f :=
        (f.sheafPushforwardContinuous (Type u) K J).map F.hom)
          (g := syPushMap K J f V))
    change F.hom.hom.app _ _ =
      (syPushMap K J f V).hom.app _ _ at hp
    exact hp.trans ((congrArg ((syPushMap K J f V).hom.app (op T.left))
      s.property).trans (syPushMap_unit K J f V T.left T.hom))⟩
  invFun s := ⟨(sectionsPullbackEquiv K
      ((f.sheafPushforwardContinuous (Type u) K J).map F.hom)
      (syPushMap K J f V) T.left).symm
        ⟨(s.val, (toSheafify K (yoneda.obj V)).app (op T.left) T.hom), by
          change F.hom.hom.app _ s.val = _
          rw [syPushMap_unit]
          exact s.property⟩, by
    change (pullback.snd ((f.sheafPushforwardContinuous (Type u) K J).map F.hom)
      (syPushMap K J f V)).hom.app (op T.left) _ = _
    exact sectionsPullbackEquiv_inv_snd K _ _ T.left _⟩
  left_inv s := by
    apply Subtype.ext
    apply (sectionsPullbackEquiv K _ _ T.left).injective
    apply Subtype.ext
    apply Prod.ext
    · exact sectionsPullbackEquiv_inv_fst K _ _ T.left _
    · exact (sectionsPullbackEquiv_inv_snd K _ _ T.left _).trans s.property.symm
  right_inv s := by
    apply Subtype.ext
    exact sectionsPullbackEquiv_inv_fst K _ _ T.left _

variable [(Over.post (X := V) f).IsContinuous (K.over V) (J.over (f.obj V))]

private def sliceRightFibreIso :
    sliceRightOver K J f V ⋙ fibreFunctor K V ≅
      fibreFunctor J (f.obj V) ⋙
        (Over.post (X := V) f).sheafPushforwardContinuous (Type u)
          (K.over V) (J.over (f.obj V)) :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun T ↦ (sliceRightFibreEquiv K J f V F T.unop).toIso)
      (by
        intro T T' b
        apply ConcreteCategory.hom_ext
        intro s
        apply Subtype.ext
        exact (pullback.fst
          ((f.sheafPushforwardContinuous (Type u) K J).map F.hom)
          (syPushMap K J f V)).hom.naturality_apply b.unop.left.op s.val))) (by
    intro F G g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (pullback.fst
        ((f.sheafPushforwardContinuous (Type u) K J).map G.hom)
        (syPushMap K J f V)).hom.app (op T.unop.left)
          (((sliceRightOver K J f V).map g).left.hom.app (op T.unop.left) s.val) =
      g.left.hom.app (op (f.obj T.unop.left))
        ((pullback.fst
          ((f.sheafPushforwardContinuous (Type u) K J).map F.hom)
          (syPushMap K J f V)).hom.app (op T.unop.left) s.val)
    have h := congrArg (fun a ↦ a.hom.app (op T.unop.left) s.val)
      (pullback.lift_fst
        (pullback.fst
          ((f.sheafPushforwardContinuous (Type u) K J).map F.hom)
          (syPushMap K J f V) ≫
            (f.sheafPushforwardContinuous (Type u) K J).map g.left)
        (pullback.snd _ _) (by
          rw [Category.assoc, ← Functor.map_comp, Over.w, pullback.condition]))
    exact h)


private def sliceEquivalence {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) :
    Sheaf (J.over U) (Type u) ≌ Over (sy J U) := by
  have : IsIso (unitTransformation J U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact unitComparison_isIso J U
  have : IsIso (counitTransformation J U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact counitComparison_isIso J U
  exact Equivalence.mk (extensionFunctor J U) (fibreFunctor J U)
    (asIso (unitTransformation J U)) (asIso (counitTransformation J U))


private def localizedLeftIso :
    (Over.post (X := V) f).sheafPullback (Type u) (K.over V) (J.over (f.obj V)) ⋙
        extensionFunctor J (f.obj V) ≅
      extensionFunctor K V ⋙ sliceLeftOver K J f V :=
  (conjugateIsoEquiv
    ((sliceEquivalence K V).toAdjunction.comp (sliceOverAdjunction K J f V))
    (((Over.post (X := V) f).sheafAdjunctionContinuous (Type u)
      (K.over V) (J.over (f.obj V))).comp (sliceEquivalence J (f.obj V)).toAdjunction)).symm
        (sliceRightFibreIso K J f V)

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

private def tensorStar {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) : Sheaf J (Type u) ⥤ Over (sy J U) where
  obj H := Over.mk (CartesianMonoidalCategory.fst (sy J U) H)
  map g := Over.homMk ((sy J U) ◁ g) (by
    exact CartesianMonoidalCategory.whiskerLeft_fst (sy J U) g)
  map_id H := by ext; simp
  map_comp g h := by ext; simp

private def restrictionFibreIso {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (U : C) :
    tensorStar J U ⋙ fibreFunctor J U ≅ J.overPullback (Type u) U :=
  NatIso.ofComponents (fun H ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun T ↦ Equiv.toIso {
      toFun s := s.val.2
      invFun s := ⟨((toSheafify J (yoneda.obj U)).app (op T.unop.left) T.unop.hom, s), rfl⟩
      left_inv s := by apply Subtype.ext; exact Prod.ext s.property.symm rfl
      right_inv s := rfl }) (by
      intro T T' b
      apply ConcreteCategory.hom_ext
      intro s
      rfl))) (by
    intro H H' g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro s
    rfl)


private def tensorStarCompIso
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] :
    tensorStar K V ⋙ sliceLeftOver K J f V ≅
      f.sheafPullback (Type u) K J ⋙ tensorStar J (f.obj V) := by
  have : IsIso (syPullbackMap K J f V) := syPullbackMap_isIso K J f V
  let L := f.sheafPullback (Type u) K J
  refine NatIso.ofComponents (fun H ↦ Over.isoMk
    (CartesianMonoidalCategory.prodComparisonIso L (sy K V) H ≪≫
      (MonoidalCategory.tensorIso (asIso (syPullbackMap K J f V)) (Iso.refl _))) ?_) ?_
  · simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Iso.refl_hom,
      asIso_hom, Functor.comp_obj, tensorStar, sliceLeftOver,
      Over.map_obj_hom, Over.mk_hom, Category.assoc,
      CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison_fst_assoc]
    rfl
  · intro H H' g
    apply Over.OverMorphism.ext
    change L.map ((sy K V) ◁ g) ≫
      (prodComparisonIso L (sy K V) H' ≪≫
        tensorIso (asIso (syPullbackMap K J f V)) (Iso.refl _)).hom =
      (prodComparisonIso L (sy K V) H ≪≫
        tensorIso (asIso (syPullbackMap K J f V)) (Iso.refl _)).hom ≫
          (sy J (f.obj V)) ◁ L.map g
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, asIso_hom,
        prodComparisonIso_hom, Category.assoc, whiskerLeft_fst, tensorHom_fst,
        CartesianMonoidalCategory.prodComparison_fst_assoc, ← L.map_comp_assoc]
    · simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, asIso_hom,
        prodComparisonIso_hom, Category.assoc, whiskerLeft_snd, tensorHom_snd,
        CartesianMonoidalCategory.prodComparison_snd_assoc,
        CartesianMonoidalCategory.prodComparison_snd, tensorHom_snd_assoc,
        Category.comp_id]
      simp only [Category.id_comp, ← L.map_comp, whiskerLeft_snd]

private def leftFibreMap :
    fibreFunctor K V ⋙
        (Over.post (X := V) f).sheafPullback (Type u) (K.over V) (J.over (f.obj V)) ⟶
      sliceLeftOver K J f V ⋙ fibreFunctor J (f.obj V) :=
  ((mateEquiv (sliceOverAdjunction K J f V)
    ((Over.post (X := V) f).sheafAdjunctionContinuous (Type u)
      (K.over V) (J.over (f.obj V)))).symm
    (TwoSquare.mk _ _ _ _ (sliceRightFibreIso K J f V).hom)).natTrans

private theorem leftFibreMap_isIso : IsIso (leftFibreMap K J f V) := by
  exact equivalentMate_isIso (sliceOverAdjunction K J f V)
    ((Over.post (X := V) f).sheafAdjunctionContinuous (Type u)
      (K.over V) (J.over (f.obj V)))
    (sliceEquivalence K V).symm (sliceEquivalence J (f.obj V)).symm
    (sliceRightFibreIso K J f V)

private def leftFibreIso :
    fibreFunctor K V ⋙
        (Over.post (X := V) f).sheafPullback (Type u) (K.over V) (J.over (f.obj V)) ≅
      sliceLeftOver K J f V ⋙ fibreFunctor J (f.obj V) := by
  have := leftFibreMap_isIso K J f V
  exact asIso (leftFibreMap K J f V)

private def geometricComparison
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] :
    K.overPullback (Type u) V ⋙
        (Over.post (X := V) f).sheafPullback (Type u) (K.over V) (J.over (f.obj V)) ≅
      f.sheafPullback (Type u) K J ⋙ J.overPullback (Type u) (f.obj V) :=
  Functor.isoWhiskerRight (restrictionFibreIso K V).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (leftFibreIso K J f V) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tensorStarCompIso K J f V) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictionFibreIso J (f.obj V))

private def productMate
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] :
    f.sheafPushforwardContinuous (Type u) K J ⋙ tensorStar K V ⟶
      tensorStar J (f.obj V) ⋙ sliceRightOver K J f V :=
  (mateEquiv (f.sheafAdjunctionContinuous (Type u) K J)
    (sliceOverAdjunction K J f V)
    (TwoSquare.mk _ _ _ _ (tensorStarCompIso K J f V).hom)).natTrans

omit [(Over.post (X := V) f).IsContinuous (K.over V) (J.over (f.obj V))] in
private theorem sliceOver_homEquiv_fst
    (A : Over (sy K V)) (B : Over (sy J (f.obj V)))
    (g : (sliceLeftOver K J f V).obj A ⟶ B) :
    ((sliceOverAdjunction K J f V).homEquiv A B g).left ≫
        pullback.fst _ _ =
      (f.sheafAdjunctionContinuous (Type u) K J).unit.app A.left ≫
        (f.sheafPushforwardContinuous (Type u) K J).map g.left := by
  dsimp [sliceOverAdjunction, Adjunction.homEquiv, Adjunction.ofNatIsoLeft,
    sliceRightOver, Over.pullback]
  simp [Adjunction.comp_unit_app, Over.mapPullbackAdj_unit_app,
    Over.postAdjunctionRight_unit_app]



omit [(Over.post (X := V) f).IsContinuous (K.over V) (J.over (f.obj V))] in
private theorem productMate_snd
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] (H : Sheaf J (Type u)) :
    ((productMate K J f V).app H).left ≫ pullback.fst _ _ ≫
        (f.sheafPushforwardContinuous (Type u) K J).map (snd (sy J (f.obj V)) H) =
      snd (sy K V) ((f.sheafPushforwardContinuous (Type u) K J).obj H) := by
  have : IsIso (syPullbackMap K J f V) := syPullbackMap_isIso K J f V
  let adj := f.sheafAdjunctionContinuous (Type u) K J
  let L := f.sheafPullback (Type u) K J
  let R := f.sheafPushforwardContinuous (Type u) K J
  have hh := sliceOver_homEquiv_fst K J f V
    ((tensorStar K V).obj (R.obj H)) ((tensorStar J (f.obj V)).obj H)
    ((tensorStarCompIso K J f V).hom.app (R.obj H) ≫
      (tensorStar J (f.obj V)).map (adj.counit.app H))
  have he : (productMate K J f V).app H =
      (sliceOverAdjunction K J f V).homEquiv _ _
        ((tensorStarCompIso K J f V).hom.app (R.obj H) ≫
          (tensorStar J (f.obj V)).map (adj.counit.app H)) := by
    simp [productMate, mateEquiv, Adjunction.homEquiv_unit, adj, R]
  rw [he]
  rw [← Category.assoc]
  erw [hh]
  rw [Category.assoc, ← R.map_comp]
  have hc :
      ((tensorStarCompIso K J f V).hom.app (R.obj H) ≫
        (tensorStar J (f.obj V)).map (adj.counit.app H)).left ≫
          snd (sy J (f.obj V)) H =
      L.map (snd (sy K V) (R.obj H)) ≫ adj.counit.app H := by
    change (prodComparisonIso L (sy K V) (R.obj H) ≪≫
      tensorIso (asIso (syPullbackMap K J f V)) (Iso.refl _)).hom ≫
        (sy J (f.obj V)) ◁ adj.counit.app H ≫ snd (sy J (f.obj V)) H = _
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc,
      whiskerLeft_snd, tensorHom_snd_assoc, Category.id_comp,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd_assoc]
  rw [hc, R.map_comp, ← Category.assoc]
  change (adj.unit.app _ ≫ R.map (L.map (snd (sy K V) (R.obj H)))) ≫
    R.map (adj.counit.app H) = _
  have hn := adj.unit.naturality (snd (sy K V) (R.obj H))
  change snd (sy K V) (R.obj H) ≫ adj.unit.app (R.obj H) =
    adj.unit.app _ ≫ R.map (L.map (snd (sy K V) (R.obj H))) at hn
  rw [← hn, Category.assoc, adj.right_triangle_components, Category.comp_id]

private theorem productMate_fibre
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] (H : Sheaf J (Type u)) :
    (fibreFunctor K V).map ((productMate K J f V).app H) ≫
        (sliceRightFibreIso K J f V).hom.app ((tensorStar J (f.obj V)).obj H) ≫
        ((Over.post (X := V) f).sheafPushforwardContinuous (Type u)
          (K.over V) (J.over (f.obj V))).map
            ((restrictionFibreIso J (f.obj V)).hom.app H) =
      (restrictionFibreIso K V).hom.app
        ((f.sheafPushforwardContinuous (Type u) K J).obj H) ≫
      (sliceSetPushforwardIso (K := K) (J := J) f V).hom.app H := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro s
  have hh := congrArg (fun a ↦ a.hom.app (op T.unop.left) s.val)
    (productMate_snd K J f V H)
  exact hh


private theorem geometricComparison_unit
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] (H : Sheaf K (Type u)) :
    ((Over.post (X := V) f).sheafAdjunctionContinuous (Type u)
        (K.over V) (J.over (f.obj V))).unit.app (H.over V) ≫
      ((Over.post (X := V) f).sheafPushforwardContinuous (Type u)
        (K.over V) (J.over (f.obj V))).map
          ((geometricComparison K J f V).hom.app H) =
      (K.overPullback (Type u) V).map
        ((f.sheafAdjunctionContinuous (Type u) K J).unit.app H) ≫
      (sliceSetPushforwardIso (K := K) (J := J) f V).hom.app
        ((f.sheafPullback (Type u) K J).obj H) := by
  let Lg := f.sheafPullback (Type u) K J
  let Rg := f.sheafPushforwardContinuous (Type u) K J
  let Lv := (Over.post (X := V) f).sheafPullback (Type u)
    (K.over V) (J.over (f.obj V))
  let Rv := (Over.post (X := V) f).sheafPushforwardContinuous (Type u)
    (K.over V) (J.over (f.obj V))
  let Lo := sliceLeftOver K J f V
  let Ro := sliceRightOver K J f V
  let ag := f.sheafAdjunctionContinuous (Type u) K J
  let av := (Over.post (X := V) f).sheafAdjunctionContinuous (Type u)
    (K.over V) (J.over (f.obj V))
  let ao := sliceOverAdjunction K J f V
  let A := tensorStar K V
  let B := tensorStar J (f.obj V)
  let P := fibreFunctor K V
  let Q := fibreFunctor J (f.obj V)
  let i := restrictionFibreIso K V
  let j := restrictionFibreIso J (f.obj V)
  let c := tensorStarCompIso K J f V
  let d := leftFibreIso K J f V
  let e := sliceRightFibreIso K J f V
  let b := productMate K J f V
  change av.unit.app (H.over V) ≫ Rv.map
    (Lv.map (i.inv.app H) ≫ d.hom.app (A.obj H) ≫
      Q.map (c.hom.app H) ≫ j.hom.app (Lg.obj H)) = _
  simp only [Functor.map_comp]
  have hn := av.unit.naturality (i.inv.app H)
  change i.inv.app H ≫ av.unit.app (P.obj (A.obj H)) =
    av.unit.app (H.over V) ≫ Rv.map (Lv.map (i.inv.app H)) at hn
  rw [← reassoc_of% hn]
  have hd := unit_mateEquiv_symm ao av (TwoSquare.mk _ _ _ _ e.hom) (A.obj H)
  change P.map (ao.unit.app (A.obj H)) ≫ e.hom.app (Lo.obj (A.obj H)) =
    av.unit.app (P.obj (A.obj H)) ≫ Rv.map (d.hom.app (A.obj H)) at hd
  rw [← reassoc_of% hd]
  have he := e.hom.naturality (c.hom.app H)
  change P.map (Ro.map (c.hom.app H)) ≫ e.hom.app (B.obj (Lg.obj H)) =
    e.hom.app (Lo.obj (A.obj H)) ≫ Rv.map (Q.map (c.hom.app H)) at he
  rw [← reassoc_of% he, ← P.map_comp_assoc]
  have hc := unit_mateEquiv ag ao (TwoSquare.mk _ _ _ _ c.hom) H
  change A.map (ag.unit.app H) ≫ b.app (Lg.obj H) =
    ao.unit.app (A.obj H) ≫ Ro.map (c.hom.app H) at hc
  rw [← hc, P.map_comp]
  have hi := i.inv.naturality (ag.unit.app H)
  change (K.overPullback (Type u) V).map (ag.unit.app H) ≫
      i.inv.app (Rg.obj (Lg.obj H)) =
    i.inv.app H ≫ P.map (A.map (ag.unit.app H)) at hi
  simp only [Category.assoc]
  rw [← reassoc_of% hi]
  have hb := productMate_fibre K J f V (Lg.obj H)
  change P.map (b.app (Lg.obj H)) ≫ e.hom.app (B.obj (Lg.obj H)) ≫
    Rv.map (j.hom.app (Lg.obj H)) =
      i.hom.app (Rg.obj (Lg.obj H)) ≫
        (sliceSetPushforwardIso (K := K) (J := J) f V).hom.app (Lg.obj H) at hb
  rw [hb]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem finishedSet
    [PreservesFiniteLimits (f.sheafPullback (Type u) K J)] :
    IsIso (sliceSetPullbackMap (K := K) (J := J) f V) := by
  have he := sliceSetPullbackMap_eq_of_unit (K := K) (J := J) f V
    (geometricComparison K J f V).hom (geometricComparison_unit K J f V)
  rw [← he]
  infer_instance

end CategoryTheory
namespace CategoryTheory
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J] (V : D)
  [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]

/-- Canonical localization of inverse image for set sheaves.
Source: Stacks Project, Sites, Tag 03CF, product calculation.
(blueprint: lem-weil-pbc-slice-set-pullback-isIso).

Proof: Identify slice sheaves with objects over the sheafified representable using
Tag 00Y1. The sheaf adjunction and Yoneda identify the inverse image of that
representable with the sheafified representable of u(V). Restriction is the
product projection to this object, so finite-limit preservation gives an
invertible product comparison. The induced adjunction on the over-categories
identifies this comparison's adjunct with restriction of the global unit. By
uniqueness under the slice adjunction it is the inverse mate defined here. -/
theorem sliceSetPullbackMap_isIso
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] :
    IsIso (sliceSetPullbackMap (K := K) (J := J) u V) := by
  exact finishedSet (K := K) (J := J) u V

/-- The localized inverse image preserves finite limits.
Source: Stacks Tag 03CF, middle diagram and the equivalence of Tag 00Y1
(blueprint: lem-weil-pbc-slice-set-pullback-isIso).
Proof: transport the localized inverse image through the equivalences with
sheaves over the sheafified representables. There it is Over.post of the global
inverse image followed by transport along the representable isomorphism.
Both preserve finite limits, and equivalences preserve and reflect them. -/
theorem sliceSetPullback_preservesFiniteLimits
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] :
    PreservesFiniteLimits ((Over.post (X := V) u).sheafPullback (Type u)
      (K.over V) (J.over (u.obj V))) := by
  let : IsIso (syPullbackMap K J u V) := syPullbackMap_isIso K J u V
  let : PreservesFiniteLimits (sliceLeftOver K J u V) := by
    exact comp_preservesFiniteLimits
      (Over.post (X := sy K V) (u.sheafPullback (Type u) K J))
      (Over.map (syPullbackMap K J u V))
  let : (extensionFunctor K V).IsEquivalence := (sliceEquivalence K V).isEquivalence_functor
  let : (extensionFunctor J (u.obj V)).IsEquivalence :=
    (sliceEquivalence J (u.obj V)).isEquivalence_functor
  let : PreservesFiniteLimits (extensionFunctor K V ⋙ sliceLeftOver K J u V) :=
    comp_preservesFiniteLimits (extensionFunctor K V) (sliceLeftOver K J u V)
  let : PreservesFiniteLimits
      ((Over.post (X := V) u).sheafPullback (Type u)
        (K.over V) (J.over (u.obj V)) ⋙ extensionFunctor J (u.obj V)) :=
    preservesFiniteLimits_of_natIso (localizedLeftIso K J u V).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (extensionFunctor J (u.obj V))

end CategoryTheory
