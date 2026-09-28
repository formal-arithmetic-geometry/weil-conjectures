/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# Small modules are presentable

Let `κ` be a regular cardinal and `R` a ring of cardinality `< κ`. We show that a module
`M : ModuleCat R` of cardinality `< κ` is a `κ`-presentable object of `ModuleCat R`.

The proof reduces to the case of types (`HasCardinalLT.isCardinalPresentable`), using that the
forgetful functor `ModuleCat R ⥤ Type` preserves filtered colimits: a linear map
`M ⟶ colim N` lifts as a function to some stage `N j`, and the `< κ` conditions expressing the
additivity and `R`-linearity of that lift hold at some later stage.

## Main results

- `ModuleCat.isCardinalPresentable_of_hasCardinalLT`: a module of cardinality `< κ` over a ring
  of cardinality `< κ` is `κ`-presentable.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- If `κ` is a regular cardinal, `R` is a ring of cardinality `< κ` and `M` is an `R`-module
of cardinality `< κ`, then `M` is a `κ`-presentable object of `ModuleCat R`. -/
lemma isCardinalPresentable_of_hasCardinalLT (M : ModuleCat.{u} R) (κ : Cardinal.{u})
    [Fact κ.IsRegular] (hR : HasCardinalLT R κ) (hM : HasCardinalLT M κ) :
    IsCardinalPresentable M κ where
  preservesColimitOfShape J _ _ := ⟨fun {N} ↦ ⟨fun {c} hc ↦ ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    have hc' := isColimitOfPreserves (forget (ModuleCat.{u} R)) hc
    have := hM.isCardinalPresentable
    have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
    have : IsCardinalPresentable (Prod (M : Type u) (M : Type u)) κ :=
      (hasCardinalLT_prod' hκ hM hM).isCardinalPresentable
    have : IsCardinalPresentable (Prod R (M : Type u)) κ :=
      (hasCardinalLT_prod' hκ hR hM).isCardinalPresentable
    refine Types.FilteredColimit.isColimitOf' _ _ (fun (g : M ⟶ c.pt) ↦ ?_)
      (fun j (g₁ g₂ : M ⟶ N.obj j) h ↦ ?_)
    · -- lift `g` as a function, then make it additive, then `R`-linear, at later stages
      obtain ⟨j, g', hg'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc'
        (X := (M : Type u)) (↾fun x ↦ g x)
      let g₀ : M → N.obj j := g'
      have hg'x (x : M) : c.ι.app j (g₀ x) = g x := ConcreteCategory.congr_hom hg' x
      obtain ⟨k, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hc'
        (X := Prod (M : Type u) (M : Type u)) (↾fun x ↦ g₀ (x.1 + x.2))
        (↾fun x ↦ g₀ x.1 + g₀ x.2) (by
          ext x
          change c.ι.app j (g₀ (x.1 + x.2)) = c.ι.app j (g₀ x.1 + g₀ x.2)
          rw [map_add, hg'x, hg'x, hg'x, map_add])
      let g'' : M → N.obj k := fun x ↦ N.map a (g₀ x)
      have hg'' (x : M) : c.ι.app k (g'' x) = g x := by
        rw [← hg'x]
        exact (ConcreteCategory.congr_hom (c.w a) (g₀ x))
      have hadd (x y : M) : g'' (x + y) = g'' x + g'' y := by
        have := ConcreteCategory.congr_hom ha ((x, y) : Prod (M : Type u) (M : Type u))
        simpa [g''] using this
      obtain ⟨l, b, hb⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hc'
        (X := Prod R (M : Type u)) (↾fun x ↦ g'' (x.1 • x.2)) (↾fun x ↦ x.1 • g'' x.2) (by
          ext x
          change c.ι.app k (g'' (x.1 • x.2)) = c.ι.app k (x.1 • g'' x.2)
          rw [hg'', map_smul, map_smul, hg''])
      refine ⟨l, ofHom
        { toFun x := N.map b (g'' x)
          map_add' x y := by rw [hadd, map_add]
          map_smul' r x := by
            have := ConcreteCategory.congr_hom hb ((r, x) : Prod R (M : Type u))
            simpa using this }, ?_⟩
      refine (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_) : g = _)
      change g x = c.ι.app l (N.map b (g'' x))
      rw [← hg'']
      exact (ConcreteCategory.congr_hom (c.w b) (g'' x)).symm
    · -- two linear maps which agree in the colimit agree as functions at a later stage
      obtain ⟨k, a, ha⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hc'
        (X := (M : Type u)) (↾fun x ↦ g₁ x) (↾fun x ↦ g₂ x) (by
          ext x
          exact ConcreteCategory.congr_hom h x)
      exact ⟨k, a, by
        change g₁ ≫ N.map a = g₂ ≫ N.map a
        ext x
        exact ConcreteCategory.congr_hom ha x⟩⟩⟩⟩

end ModuleCat
