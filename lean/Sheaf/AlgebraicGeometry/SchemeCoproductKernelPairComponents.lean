/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Kernel pairs restricted to scheme coproduct components

Source: Stacks Project, Spaces, Tags 0262, 02WV and 02WW.
(blueprint: lem-trf-scheme-coproduct-kernel-pair-components)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Even for a large indexing type, a specified scheme coproduct has open injections. -/
private theorem cofan_open {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j)) (i : J) :
    IsOpenImmersion (j i) := by
  classical
  let k : ∀ a, X a ⟶ X i ⨿ Y := fun a ↦
    if e : a = i then eqToHom (congrArg X e) ≫ coprod.inl else j a ≫ coprod.inr
  let δ : Y ⟶ X i ⨿ Y := Cofan.IsColimit.desc h k
  have fac (a : J) : j a ≫ δ = k a := Cofan.IsColimit.fac h k a
  have hi : j i ≫ δ = coprod.inl := by simpa [k] using fac i
  have hr : δ ≫ coprod.desc (j i) (𝟙 Y) = 𝟙 Y := by
    apply Cofan.IsColimit.hom_ext h
    intro a
    change j a ≫ δ ≫ coprod.desc (j i) (𝟙 Y) = j a ≫ 𝟙 Y
    rw [← Category.assoc, fac]
    by_cases e : a = i
    · subst a; simp [k]
    · simp [k, e, Category.assoc]
  have pb : IsPullback (𝟙 (X i)) (j i) coprod.inl δ := by
    apply IsPullback.mk' (by simpa using hi.symm)
    · intro W f g hf _
      simpa using hf
    · intro W a b hab
      refine ⟨a, by simp, ?_⟩
      have hh := congrArg (fun t ↦ t ≫ coprod.desc (j i) (𝟙 Y)) hab
      simpa [Category.assoc, hr] using hh
  exact MorphismProperty.of_isPullback pb inferInstance

private theorem cofan_covers {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j)) :
    ∀ y : Y, ∃ i x, j i x = y := by
  let : ∀ i, IsOpenImmersion (j i) := cofan_open X Y j h
  let W : Y.Opens := ⨆ i, (j i).opensRange
  let k : ∀ i, X i ⟶ W.toScheme := fun i ↦
    IsOpenImmersion.lift W.ι (j i) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨j i x, le_iSup (fun i ↦ (j i).opensRange) i ⟨x, rfl⟩⟩, rfl⟩)
  let t := Cofan.IsColimit.desc h k
  have ht : t ≫ W.ι = 𝟙 Y := by
    apply Cofan.IsColimit.hom_ext h
    intro i
    change j i ≫ t ≫ W.ι = j i ≫ 𝟙 Y
    have hf : j i ≫ t = k i := Cofan.IsColimit.fac h k i
    rw [← Category.assoc, hf]
    exact (IsOpenImmersion.lift_fac _ _ _).trans (Category.comp_id _).symm
  intro y
  have hy : y ∈ W := by
    have he := congrArg (fun f : Y ⟶ Y ↦ f y) ht
    change W.ι (t y) = y at he
    exact he ▸ (t y).property
  obtain ⟨i, x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i, x, hx⟩

private theorem cofan_disjoint {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j))
    {i k : J} (hik : i ≠ k) (x : X i) (y : X k) : j i x ≠ j k y := by
  classical
  let f : ∀ a, X a ⟶ Y ⨿ Y := fun a ↦
    j a ≫ if a = i then coprod.inl else coprod.inr
  let t := Cofan.IsColimit.desc h f
  have hi : j i ≫ t = j i ≫ coprod.inl := by
    simpa [f] using Cofan.IsColimit.fac h f i
  have hk : j k ≫ t = j k ≫ coprod.inr := by
    simpa [f, Ne.symm hik] using Cofan.IsColimit.fac h f k
  intro he
  apply inl_ne_inr Y Y (j i x) (j k y)
  calc
    (coprod.inl : Y ⟶ Y ⨿ Y) (j i x) = t (j i x) :=
      (congrArg (fun f : X i ⟶ Y ⨿ Y ↦ f x) hi).symm
    _ = t (j k y) := congrArg t he
    _ = (coprod.inr : Y ⟶ Y ⨿ Y) (j k y) := congrArg (fun f : X k ⟶ Y ⨿ Y ↦ f y) hk

/-- A scheme coproduct presentation restricts to its individual kernel-pair squares.
Source: Stacks Project, Spaces, Tag 0262, sectionwise kernel-pair formula;
Tags 02WV and 02WW (blueprint: lem-trf-scheme-coproduct-kernel-pair-components).

Proof: On a test scheme T, lift a pair of maps to X_i and X_j with equal quotient
sections through the assumed kernel-pair square to W. The coproduct injections are
open immersions with disjoint images. Every point of W lies in one component R_ab;
its two images lie in X_a and X_b. Since the two projections of the lift lie in
X_i and X_j, disjointness forces a=i and b=j. Thus the lift has image in R_ij,
and the open-immersion lifting property gives a unique map T to R_ij. This works
also for empty T. Uniqueness follows from the kernel-pair square and monicity of
the coproduct injection. These lifting and uniqueness properties on all tests,
which commute with restriction, give the asserted presheaf pullback square. -/
theorem scheme_coproduct_kernel_pair_components
    {S : Scheme.{u}} {I : Type v} (X : I → Over S) (R : I → I → Over S)
    (p : ∀ i j, R i j ⟶ X i)
    (t' : ∀ i j, R i j ⟶ X j)
    (V W : Over S) (ι : ∀ i, X i ⟶ V) (κ : ∀ ij : I × I, R ij.1 ij.2 ⟶ W)
    (hV : IsColimit (Cofan.mk V ι)) (hW : IsColimit (Cofan.mk W κ))
    (s t : W ⟶ V)
    (hs : ∀ i j, κ (i, j) ≫ s = p i j ≫ ι i)
    (ht : ∀ i j, κ (i, j) ≫ t = t' i j ≫ ι j)
    {F : (Over S)ᵒᵖ ⥤ Type u} (q : yoneda.obj V ⟶ F)
    (hkernel : IsPullback (yoneda.map s) (yoneda.map t) q q) :
    ∀ i j, IsPullback (yoneda.map (p i j)) (yoneda.map (t' i j))
      (yoneda.map (ι i) ≫ q) (yoneda.map (ι j) ≫ q) := by
  classical
  have hVl : IsColimit (Cofan.mk V.left (fun i ↦ (ι i).left)) :=
    isColimitCofanMkObjOfIsColimit (Over.forget S) X ι hV
  have hWl : IsColimit (Cofan.mk W.left (fun ij ↦ (κ ij).left)) :=
    isColimitCofanMkObjOfIsColimit (Over.forget S) (fun ij : I × I ↦ R ij.1 ij.2) κ hW
  have (i : I) : IsOpenImmersion (ι i).left := cofan_open _ _ _ hVl i
  have (ij : I × I) : IsOpenImmersion (κ ij).left := cofan_open _ _ _ hWl ij
  have lift_component (i j : I) (T : Over S) (x : T ⟶ X i) (y : T ⟶ X j)
      (hxy : (yoneda.map (ι i) ≫ q).app (op T) x =
        (yoneda.map (ι j) ≫ q).app (op T) y) :
      ∃ l : T ⟶ R i j, l ≫ p i j = x ∧ l ≫ t' i j = y := by
    obtain ⟨r, hr, hr'⟩ := Types.exists_of_isPullback
      (hkernel.app (op T)) (x ≫ ι i) (y ≫ ι j) hxy
    change r ≫ s = x ≫ ι i at hr
    change r ≫ t = y ≫ ι j at hr'
    have range_r : Set.range r.left ⊆ Set.range (κ (i, j)).left := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨⟨a, b⟩, w, hw⟩ := cofan_covers _ _ _ hWl (r.left z)
      have ha : a = i := by
        by_contra hn
        apply cofan_disjoint _ _ _ hVl hn ((p a b).left w) (x.left z)
        calc
          (ι a).left ((p a b).left w) = s.left ((κ (a, b)).left w) :=
            (congrArg (fun f ↦ f.left w) (hs a b)).symm
          _ = s.left (r.left z) := congrArg s.left hw
          _ = (ι i).left (x.left z) := congrArg (fun f ↦ f.left z) hr
      have hb : b = j := by
        by_contra hn
        apply cofan_disjoint _ _ _ hVl hn ((t' a b).left w) (y.left z)
        calc
          (ι b).left ((t' a b).left w) = t.left ((κ (a, b)).left w) :=
            (congrArg (fun f ↦ f.left w) (ht a b)).symm
          _ = t.left (r.left z) := congrArg t.left hw
          _ = (ι j).left (y.left z) := congrArg (fun f ↦ f.left z) hr'
      subst a; subst b
      exact ⟨w, hw⟩
    let l : T ⟶ R i j := Over.homMk
      (IsOpenImmersion.lift (κ (i, j)).left r.left range_r) (by
        rw [← Over.w (κ (i, j)), ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have hl : l ≫ κ (i, j) = r := by
      apply Over.OverMorphism.ext
      exact IsOpenImmersion.lift_fac _ _ _
    refine ⟨l, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      apply (cancel_mono (ι i).left).mp
      change (l ≫ p i j ≫ ι i).left = (x ≫ ι i).left
      rw [← hs, ← Category.assoc, hl, hr]
    · apply Over.OverMorphism.ext
      apply (cancel_mono (ι j).left).mp
      change (l ≫ t' i j ≫ ι j).left = (y ≫ ι j).left
      rw [← ht, ← Category.assoc, hl, hr']
  intro i j
  have w : yoneda.map (p i j) ≫ (yoneda.map (ι i) ≫ q) =
      yoneda.map (t' i j) ≫ (yoneda.map (ι j) ≫ q) := by
    rw [← Category.assoc, ← Functor.map_comp, ← hs,
      ← Category.assoc, ← Functor.map_comp, ← ht,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hkernel.w]
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨NatTrans.congr_app w T, ?_, ?_⟩
  · intro a b hab
    apply Over.OverMorphism.ext
    apply (cancel_mono (κ (i, j)).left).mp
    have he : a ≫ κ (i, j) = b ≫ κ (i, j) := by
      apply Types.ext_of_isPullback (hkernel.app T)
      · change a ≫ κ (i, j) ≫ s = b ≫ κ (i, j) ≫ s
        rw [hs, ← Category.assoc, ← Category.assoc]
        exact congrArg (fun z ↦ z ≫ ι i) hab.1
      · change a ≫ κ (i, j) ≫ t = b ≫ κ (i, j) ≫ t
        rw [ht, ← Category.assoc, ← Category.assoc]
        exact congrArg (fun z ↦ z ≫ ι j) hab.2
    exact congrArg CommaMorphism.left he
  · intro x y hxy
    exact lift_component i j T.unop x y hxy

end AlgebraicGeometry.AlgebraicSpace
