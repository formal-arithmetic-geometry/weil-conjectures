/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.CategoryTheory.Abelian.ExtFilteredColimit

/-!
# `Ext` as morphisms in the bounded below derived category

For objects `A` and `N` of an abelian category `C`, maps `A[0] ⟶ N[0]⟦n⟧` in `D⁺(C)` are the
`Ext`-groups `Extⁿ(A, N)` for `n ≥ 0`, and vanish for `n < 0`. As a consequence, if the
functors `Extⁿ(A, -)` commute with filtered colimits of shape `J`, so do the functors
`N ↦ Hom(A[0], N[0]⟦q⟧)` on `C`.

## Main definitions

- `DerivedCategory.Plus.shiftedHomAddEquivExt`: `Hom(A[0], N[0]⟦n⟧) ≃+ Extⁿ(A, N)`.

## Main statements

- `DerivedCategory.Plus.subsingleton_shiftedHom_of_neg`: `Hom(A[0], N[0]⟦q⟧) = 0` for `q < 0`.
- `DerivedCategory.Plus.preservesColimitsOfShape_shiftedHom`: the functor
  `N ↦ Hom(A[0], N[0]⟦q⟧)` commutes with filtered colimits of shape `J` if the functors
  `Extⁿ(A, -)` do.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits Opposite Abelian

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

/-- The comparison of maps `A[0] ⟶ N[0]⟦q⟧` in `D⁺(C)` with maps in `D(C)`. -/
noncomputable def shiftedHomEquiv (A N : C) (q : ℤ) :
    ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) ≃
      ((DerivedCategory.singleFunctor C 0).obj A ⟶
        ((DerivedCategory.singleFunctor C 0).obj N)⟦q⟧) :=
  ((ObjectProperty.fullyFaithfulι _).homEquiv).trans
    (((singleFunctorιIso C 0).app A).homCongr ((Plus.ι.commShiftIso q).app _ ≪≫
      (shiftFunctor _ q).mapIso ((singleFunctorιIso C 0).app N)))

lemma shiftedHomEquiv_apply (A N : C) (q : ℤ)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :
    shiftedHomEquiv A N q f = ((singleFunctorιIso C 0).app A).inv ≫ Plus.ι.map f ≫
      (Plus.ι.commShiftIso q).hom.app _ ≫
        (shiftFunctor _ q).map ((singleFunctorιIso C 0).hom.app N) := by
  rfl

lemma shiftedHomEquiv_add (A N : C) (q : ℤ)
    (f g : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :
    shiftedHomEquiv A N q (f + g) = shiftedHomEquiv A N q f + shiftedHomEquiv A N q g := by
  simp only [shiftedHomEquiv_apply, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

lemma shiftedHomEquiv_comp (A : C) {N N' : C} (q : ℤ)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) (g : N ⟶ N') :
    shiftedHomEquiv A N' q (f ≫ (shiftFunctor _ q).map ((singleFunctor C 0).map g)) =
      shiftedHomEquiv A N q f ≫
        (shiftFunctor _ q).map ((DerivedCategory.singleFunctor C 0).map g) := by
  simp only [shiftedHomEquiv_apply, Functor.map_comp, Category.assoc]
  congr 2
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (singleFunctorιIso C 0).hom.naturality g

lemma shiftedHomEquiv_precomp {A A' : C} (N : C) (q : ℤ) (g : A' ⟶ A)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :
    shiftedHomEquiv A' N q ((singleFunctor C 0).map g ≫ f) =
      (DerivedCategory.singleFunctor C 0).map g ≫ shiftedHomEquiv A N q f := by
  simp only [shiftedHomEquiv_apply, Functor.map_comp, Category.assoc]
  rw [Iso.app_inv, Iso.app_inv]
  exact ((singleFunctorιIso C 0).inv.naturality_assoc g _).symm

/-- Maps `A[0] ⟶ N[0]⟦q⟧` in `D⁺(C)` vanish for `q < 0`. -/
lemma subsingleton_shiftedHom_of_neg (A N : C) (q : ℤ) (hq : q < 0) :
    Subsingleton ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) := by
  have : DerivedCategory.TStructure.t.IsGE (((DerivedCategory.singleFunctor C 0).obj N)⟦q⟧) (-q) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 q (-q)
  refine ⟨fun f g ↦ (shiftedHomEquiv A N q).injective ?_⟩
  rw [DerivedCategory.TStructure.t.zero (shiftedHomEquiv A N q f) 0 (-q),
    DerivedCategory.TStructure.t.zero (shiftedHomEquiv A N q g) 0 (-q)]

variable [HasExt.{w} C]

/-- Maps `A[0] ⟶ N[0]⟦n⟧` in `D⁺(C)` are the `Ext`-group `Extⁿ(A, N)`. -/
noncomputable def shiftedHomAddEquivExt (A N : C) (n : ℕ) :
    ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦(n : ℤ)⟧) ≃+ Ext.{w} A N n :=
  AddEquiv.trans
    { toEquiv := shiftedHomEquiv A N n
      map_add' := shiftedHomEquiv_add A N n }
    Ext.homAddEquiv.symm

lemma shiftedHomAddEquivExt_comp (A : C) {N N' : C} (n : ℕ)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦(n : ℤ)⟧) (g : N ⟶ N') :
    shiftedHomAddEquivExt A N' n (f ≫ (shiftFunctor _ (n : ℤ)).map ((singleFunctor C 0).map g)) =
      (shiftedHomAddEquivExt A N n f).comp (Ext.mk₀ g) (add_zero n) := by
  have key {N : C} (x : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      ((DerivedCategory.singleFunctor C 0).obj N) (n : ℤ)) :
      (Ext.homAddEquiv.symm x : Ext.{w} A N n).hom = x :=
    Ext.homAddEquiv.apply_symm_apply x
  refine (Ext.homAddEquiv (X := A) (Y := N') (n := n)).injective ?_
  rw [Ext.homAddEquiv_apply, Ext.homAddEquiv_apply, ← Ext.hom_comp_singleFunctor_map_shift]
  simp only [shiftedHomAddEquivExt, AddEquiv.trans_apply, AddEquiv.coe_mk]
  rw [key, key]
  exact shiftedHomEquiv_comp A n f g

lemma shiftedHomAddEquivExt_precomp {A A' : C} (N : C) (n : ℕ) (g : A' ⟶ A)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦(n : ℤ)⟧) :
    shiftedHomAddEquivExt A' N n ((singleFunctor C 0).map g ≫ f) =
      (Ext.mk₀ g).comp (shiftedHomAddEquivExt A N n f) (zero_add n) := by
  have key {A : C} (x : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      ((DerivedCategory.singleFunctor C 0).obj N) (n : ℤ)) :
      (Ext.homAddEquiv.symm x : Ext.{w} A N n).hom = x :=
    Ext.homAddEquiv.apply_symm_apply x
  refine (Ext.homAddEquiv (X := A') (Y := N) (n := n)).injective ?_
  rw [Ext.homAddEquiv_apply, Ext.homAddEquiv_apply, Ext.comp_hom, Ext.mk₀_hom]
  simp only [shiftedHomAddEquivExt, AddEquiv.trans_apply, AddEquiv.coe_mk]
  rw [key, key, ShiftedHom.mk₀_comp]
  exact shiftedHomEquiv_precomp N n g f

section Colimits

variable {J : Type*} [Category J] [IsFiltered J]

/-- If the functors `Extⁿ(A, -)` commute with colimits of the filtered shape `J`, in the sense
of `CategoryTheory.Abelian.Ext.CommutesWithColimit`, then so does the functor
`N ↦ Hom(A[0], N[0]⟦q⟧)` on `C`, for every `q : ℤ`. -/
lemma preservesColimitsOfShape_shiftedHom (A : C) (q : ℤ)
    [HasColimitsOfShape J AddCommGrpCat.{w'}]
    [PreservesColimitsOfShape J (CategoryTheory.forget AddCommGrpCat.{w'})]
    (h : ∀ (n : ℕ) (D : J ⥤ C) (c : Cocone D), IsColimit c → Ext.CommutesWithColimit.{w} A n c) :
    PreservesColimitsOfShape J (singleFunctor C 0 ⋙ shiftFunctor (Plus C) q ⋙
      preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj A))) := by
  let F := singleFunctor C 0 ⋙ shiftFunctor (Plus C) q ⋙
    preadditiveCoyoneda.obj (op ((singleFunctor C 0).obj A))
  have hF {N N' : C} (g : N ⟶ N') (x : (singleFunctor C 0).obj A ⟶
      ((singleFunctor C 0).obj N)⟦q⟧) :
      F.map g x = x ≫ (shiftFunctor _ q).map ((singleFunctor C 0).map g) := rfl
  have : ReflectsColimitsOfShape J (CategoryTheory.forget AddCommGrpCat.{w'}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨fun {D} ↦ ⟨fun {c} hc ↦ ?_⟩⟩
  rcases lt_or_ge q 0 with hq | hq
  · have (N : C) : Subsingleton ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :=
      subsingleton_shiftedHom_of_neg A N q hq
    refine ⟨isColimitOfReflects (CategoryTheory.forget AddCommGrpCat)
      (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun i x y _ ↦ ⟨i, 𝟙 i, Subsingleton.elim (α := (singleFunctor C 0).obj A ⟶
        ((singleFunctor C 0).obj (D.obj i))⟦q⟧) _ _⟩))⟩
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact ⟨j, 0, Subsingleton.elim (α := (singleFunctor C 0).obj A ⟶
      ((singleFunctor C 0).obj c.pt)⟦q⟧) _ _⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let φ (N : C) := shiftedHomAddEquivExt.{w} A N n
    refine ⟨isColimitOfReflects (CategoryTheory.forget AddCommGrpCat)
      (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun i x y hxy ↦ ?_))⟩
    · obtain ⟨j, y, hy⟩ := (h n D c hc).1 (φ c.pt x)
      refine ⟨j, (φ _).symm y, (φ c.pt).injective ?_⟩
      change _ = φ c.pt (F.map (c.ι.app j) ((φ _).symm y))
      rw [hF, shiftedHomAddEquivExt_comp, AddEquiv.apply_symm_apply, hy]
    · change F.map (c.ι.app i) x = F.map (c.ι.app i) y at hxy
      obtain ⟨k, f, hf⟩ := (h n D c hc).2 i (φ _ (x - y)) (by
        rw [map_sub, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, ← sub_eq_add_neg, sub_eq_zero,
          ← shiftedHomAddEquivExt_comp, ← shiftedHomAddEquivExt_comp, ← hF, ← hF, hxy])
      refine ⟨k, f, ?_⟩
      change F.map (D.map f) x = F.map (D.map f) y
      rw [map_sub, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, ← sub_eq_add_neg, sub_eq_zero,
        ← shiftedHomAddEquivExt_comp, ← shiftedHomAddEquivExt_comp, ← hF, ← hF] at hf
      exact (φ _).injective hf

end Colimits

end DerivedCategory.Plus
