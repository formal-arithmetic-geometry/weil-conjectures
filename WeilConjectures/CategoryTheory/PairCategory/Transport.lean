/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PairCategory.Shift

/-!
# Transport between stages of the pair category

For stages `k ≤ m` of a pair category `PairCategory F`, the inclusion `j_k` of the stage `k` is
isomorphic to `T_{m/k} ⋙ j_m`, through the isomorphisms `(k, A) ≅ (m, T_{m/k} A)` of
`PairCategory.isoToStage`. When the stages carry shifts, this isomorphism commutes with the
shifts. Moreover, two morphisms of the stage `k` have the same image in the pair category if
and only if they become equal at some further stage.

These are the facts of blueprint `prop-weil-pbc-common-stage-calculus` saying that every finite
diagram of the pair category is represented over one stage, and that asserted equalities hold
exactly when they hold after passage to a further common stage.

## Main definitions

- `CategoryTheory.PairCategory.inclTransIso` : the isomorphism `j_k ≅ T_{m/k} ⋙ j_m`.

## Main results

- `CategoryTheory.PairCategory.incl_map_eq_incl_map_iff` : equality of images of stage
  morphisms is detected at a further stage.
- `CategoryTheory.PairCategory.inclTransIso_commShift` : the transport isomorphism commutes
  with the shifts.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Category Limits Pseudofunctor

namespace CategoryTheory.PairCategory

variable {ι : Type w} [Preorder ι] {F : Pseudofunctor (LocallyDiscrete ι) Cat.{v, u}}
  [IsDirected ι (· ≤ ·)]

variable (F) in
/-- The isomorphism `j_k ≅ T_{m/k} ⋙ j_m` for stages `k ≤ m`: its component at `A` is
`isoToStage : (k, A) ≅ (m, T_{m/k} A)`. -/
noncomputable def inclTransIso {k m : ι} (h : k ≤ m) :
    incl F k ≅ F.transition h ⋙ incl F m :=
  NatIso.ofComponents (fun A ↦ isoToStage ((incl F k).obj A) h) (fun {A B} u ↦ by
    simp only [Functor.comp_map, isoToStage, incl, homMk_comp_homMk]
    rw [← homMk_trHom (X := (⟨k, A⟩ : PairCategory F)) (Y := ⟨k, B⟩) h le_rfl le_rfl h h]
    rw [homMk_comp_homMk]
    congr 1
    simp only [trHom, Functor.map_comp, assoc]
    rw [transitionComp_id_left F le_rfl h A, transitionComp_id_left_inv F le_rfl h B]
    simp [← Functor.map_comp_assoc, ← Functor.map_comp])

lemma inclTransIso_hom_app {k m : ι} (h : k ≤ m) (A : F.obj ⟨k⟩) :
    (inclTransIso F h).hom.app A = (isoToStage ((incl F k).obj A) h).hom :=
  rfl

lemma inclTransIso_inv_app {k m : ι} (h : k ≤ m) (A : F.obj ⟨k⟩) :
    (inclTransIso F h).inv.app A = (isoToStage ((incl F k).obj A) h).inv :=
  rfl

/-- A morphism between objects of a stage `k` represented at a stage `m ≥ k` by `u` is the
conjugate of `j_m(u)` by the transport isomorphisms. -/
lemma homMk_incl_eq {k m : ι} (h : k ≤ m) {A B : F.obj ⟨k⟩}
    (u : (F.transition h).obj A ⟶ (F.transition h).obj B) :
    homMk (X := (incl F k).obj A) (Y := (incl F k).obj B) h h u =
      (inclTransIso F h).hom.app A ≫ (incl F m).map u ≫ (inclTransIso F h).inv.app B :=
  homMk_eq _ _ _

/-- The image under `j_k` of a stage morphism is represented at any further stage `m` by its
transport `T_{m/k}(u)`. -/
lemma incl_map_eq_trans {k m : ι} (h : k ≤ m) {A B : F.obj ⟨k⟩} (u : A ⟶ B) :
    (incl F k).map u =
      (inclTransIso F h).hom.app A ≫ (incl F m).map ((F.transition h).map u) ≫
        (inclTransIso F h).inv.app B := by
  rw [← homMk_incl_eq, incl_map_eq_homMk h]

/-- Every morphism between objects of a stage `k` is, at some stage `m ≥ m₀`, the conjugate of
the image of a stage morphism. -/
lemma exists_eq_incl_map {k : ι} {A B : F.obj ⟨k⟩} (f : (incl F k).obj A ⟶ (incl F k).obj B)
    (m₀ : ι) : ∃ (m : ι) (_ : m₀ ≤ m) (h : k ≤ m)
      (u : (F.transition h).obj A ⟶ (F.transition h).obj B),
      f = (inclTransIso F h).hom.app A ≫ (incl F m).map u ≫ (inclTransIso F h).inv.app B := by
  obtain ⟨m, hm, hX, hY, u, rfl⟩ := exists_homMk_ge f m₀
  exact ⟨m, hm, hX, u, homMk_incl_eq hX u⟩

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: two morphisms of a stage have the same
image in the pair category if and only if they become equal at some further stage. -/
lemma incl_map_eq_incl_map_iff {k : ι} {A B : F.obj ⟨k⟩} (u v : A ⟶ B) :
    (incl F k).map u = (incl F k).map v ↔
      ∃ (m : ι) (h : k ≤ m), (F.transition h).map u = (F.transition h).map v := by
  rw [incl_map_eq_homMk le_rfl, incl_map_eq_homMk le_rfl, homMk_eq_homMk_iff]
  refine ⟨fun ⟨m, h, e⟩ ↦ ⟨m, h, ?_⟩, fun ⟨m, h, e⟩ ↦ ⟨m, h, ?_⟩⟩
  · simp only [trHom, cancel_epi, cancel_mono] at e
    rw [← cancel_mono ((F.transitionComp le_rfl h h).hom.app B),
      transitionComp_hom_naturality, transitionComp_hom_naturality, e]
  · simp only [trHom]
    rw [← transitionComp_hom_naturality_assoc, ← transitionComp_hom_naturality_assoc, e]

section Shift

variable (A : Type w') [AddMonoid A] [∀ i : ι, HasShift (F.obj ⟨i⟩) A]
  [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).CommShift A] [ShiftCompatible F A]

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the transport isomorphism
`j_k ≅ T_{m/k} ⋙ j_m` commutes with the shifts. -/
instance inclTransIso_commShift {k m : ι} (h : k ≤ m) :
    NatTrans.CommShift (inclTransIso F h).hom A where
  shift_comm a := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, incl_commShiftIso_hom_app, id_comp,
      inclTransIso_hom_app, isoToStage]
    erw [comp_id]
    rw [shiftFunctor_map_homMk]
    dsimp only [incl]
    rw [homMk_comp_homMk]
    congr 1
    have e := NatTrans.shift_app_comm (F.transitionId m le_rfl).hom a
      ((F.transition h).obj K)
    rw [Functor.commShiftIso_id_hom_app] at e
    erw [comp_id] at e
    have e' : ((F.transitionId m le_rfl).inv.app ((F.transition h).obj K))⟦a⟧' ≫
        ((F.transition (le_refl m)).commShiftIso a).inv.app ((F.transition h).obj K) =
          (F.transitionId m le_rfl).inv.app (((F.transition h).obj K)⟦a⟧) := by
      symm
      apply Iso.inv_ext (f := (F.transitionId m le_rfl).app
        (((F.transition h).obj K)⟦a⟧))
      rw [Iso.app_hom, ← e]
      simp [← Functor.map_comp_assoc]
    simp only [Iso.inv_hom_id_app_assoc]
    congr 1

end Shift

end CategoryTheory.PairCategory
