/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteCoproducts
public import WeilConjectures.AlgebraicGeometry.EtaleQcqsFiniteLimits

/-!
# Sections of étale sheaves over finite coproducts

A finite coproduct in the small étale site is a disjoint union of schemes. Hence sections of a
sheaf over a finite coproduct can be glued from arbitrary sections over the summands.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} {ι : Type} [Finite ι] {T : ι → X.Etale} {Z : X.Etale}
  (c : ∀ i, T i ⟶ Z) (hc : IsColimit (Cofan.mk Z c))

include hc

lemma exists_left_eq_of_isColimit (z : Z.left) : ∃ i y, (c i).left y = z := by
  let hl := isColimitCofanLeft c hc
  let e := hl.coconePointUniqueUpToIso (coproductIsCoproduct fun k ↦ (T k).left)
  obtain ⟨i, y, hy⟩ := exists_sigmaι_eq (e.hom z)
  refine ⟨i, y, ?_⟩
  have h : (c i).left ≫ e.hom = Sigma.ι (fun k ↦ (T k).left) i := by
    simpa using hl.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _) ⟨i⟩
  calc (c i).left y = e.inv (e.hom ((c i).left y)) := by
        rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
    _ = e.inv ((Sigma.ι (fun k ↦ (T k).left) i) y) := by
      rw [← h, Scheme.Hom.comp_apply]
    _ = e.inv (e.hom z) := by rw [hy]
    _ = z := by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl

lemma mono_of_isColimit (i : ι) : Mono (c i) := by
  let hl := isColimitCofanLeft c hc
  let e := hl.coconePointUniqueUpToIso (coproductIsCoproduct fun k ↦ (T k).left)
  have h₀ : (c i).left ≫ e.hom = Sigma.ι (fun k ↦ (T k).left) i := by
    simpa using hl.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _) ⟨i⟩
  have h : (c i).left = Sigma.ι _ i ≫ e.inv := by
    rw [← h₀]
    simp
  have : Mono (c i).left := by rw [h]; infer_instance
  exact (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map this

lemma isEmpty_of_comp_eq {W : X.Etale} {i j : ι} (hij : i ≠ j) (a : W ⟶ T i) (b : W ⟶ T j)
    (hab : a ≫ c i = b ≫ c j) : IsEmpty W.left := by
  let hl := isColimitCofanLeft c hc
  let e := hl.coconePointUniqueUpToIso (coproductIsCoproduct fun k ↦ (T k).left)
  have h : ∀ k, (c k).left ≫ e.hom = Sigma.ι (fun k ↦ (T k).left) k := fun k ↦ by
    simpa using hl.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _) ⟨k⟩
  refine isEmpty_of_commSq_sigmaι_of_ne (g := fun k ↦ (T k).left) (a := a.left) (b := b.left)
    ⟨?_⟩ hij
  rw [← h, ← h, ← Category.assoc, ← Category.assoc]
  congr 1
  exact congrArg (fun φ ↦ φ.left) hab

variable {A : Type u'} [Category.{u + 1} A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] (G : Sheaf X.smallEtaleTopology A)

omit hc in
lemma subsingleton_of_isEmpty {W : X.Etale} (hW : IsEmpty W.left) :
    Subsingleton (ToType (G.obj.obj (op W))) := by
  have hP := ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget A)).obj G).property
  have hmem : Sieve.ofArrows (fun e : PEmpty ↦ W) (fun e ↦ e.elim) ∈
      X.smallEtaleTopology W := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    exact hW.elim x
  have hSF := (Presieve.isSheafFor_iff_generate _).2 (((isSheaf_iff_isSheaf_of_type _ _).1 hP) _ hmem)
  rw [Presieve.isSheafFor_arrows_iff] at hSF
  obtain ⟨t, -, ht⟩ := hSF (fun e ↦ e.elim) (fun e ↦ e.elim)
  exact ⟨fun x y ↦ (ht x (fun e ↦ e.elim)).trans (ht y (fun e ↦ e.elim)).symm⟩

/-- Sections of a sheaf over the summands of a finite coproduct glue. -/
lemma exists_glue_of_isColimit (t : ∀ i, ToType (G.obj.obj (op (T i)))) :
    ∃ s : ToType (G.obj.obj (op Z)), ∀ i, G.obj.map (c i).op s = t i := by
  have hP := ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget A)).obj G).property
  have hmem : Sieve.ofArrows T c ∈ X.smallEtaleTopology Z := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext z
    obtain ⟨i, y, rfl⟩ := exists_left_eq_of_isColimit c hc z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨i, y, rfl⟩
  have hSF := (Presieve.isSheafFor_iff_generate _).2 (((isSheaf_iff_isSheaf_of_type _ _).1 hP) _ hmem)
  rw [Presieve.isSheafFor_arrows_iff] at hSF
  obtain ⟨s, hs, -⟩ := hSF t (by
    intro i j W a b hab
    by_cases hij : i = j
    · subst hij
      have := mono_of_isColimit c hc i
      obtain rfl := (cancel_mono (c i)).1 hab
      rfl
    · have := subsingleton_of_isEmpty G (isEmpty_of_comp_eq c hc hij a b hab)
      exact Subsingleton.elim _ _)
  exact ⟨s, hs⟩

/-- Sections of a sheaf over a finite coproduct are determined by their restrictions. -/
lemma ext_of_isColimit {s s' : ToType (G.obj.obj (op Z))}
    (h : ∀ i, G.obj.map (c i).op s = G.obj.map (c i).op s') : s = s' := by
  have hP := ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget A)).obj G).property
  have hmem : Sieve.ofArrows T c ∈ X.smallEtaleTopology Z := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext z
    obtain ⟨i, y, rfl⟩ := exists_left_eq_of_isColimit c hc z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨i, y, rfl⟩
  have hSF := (Presieve.isSheafFor_iff_generate _).2 (((isSheaf_iff_isSheaf_of_type _ _).1 hP) _ hmem)
  rw [Presieve.isSheafFor_arrows_iff] at hSF
  obtain ⟨t, -, ht⟩ := hSF (fun i ↦ G.obj.map (c i).op s') (by
    intro i j W a b hab
    change ((CategoryTheory.forget A).map _ ≫ (CategoryTheory.forget A).map _) _ = ((CategoryTheory.forget A).map _ ≫ (CategoryTheory.forget A).map _) _
    simp only [← Functor.map_comp, ← op_comp, hab])
  exact (ht s h).trans (ht s' fun _ ↦ rfl).symm

end AlgebraicGeometry.Scheme.Etale
