/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Objects representing linear duals of their Hom functors

Let `P` and `X` be objects of a preadditive category. The group `Hom(P, X)` is a right module
over the ring `End P`, acting by precomposition, and composition gives a pairing
`Hom(P, X) × Hom(X, P) ⟶ End P`. We say that `P` *represents the linear dual* of `Hom(P, X)`
if this pairing identifies `Hom(X, P)` with the additive `End P`-linear maps
`Hom(P, X) ⟶ End P`: every such map is composition with a unique morphism `X ⟶ P`.

For `P = R` in the category of modules over a commutative ring `R`, this holds for every
module `X`: `Hom_R(R, X) = X` and `Hom_R(X, R)` is the `R`-linear dual of `X`
(`ModuleCat.representsLinearDual_self`). The property is transported along functors which are
bijective on the relevant Hom groups (`CategoryTheory.RepresentsLinearDual.of_functor`).

## Main definitions

- `CategoryTheory.RepresentsLinearDual`: `P` represents the `End P`-linear dual of
  `Hom(P, X)`.

## Main statements

- `CategoryTheory.RepresentsLinearDual.of_functor`: transport along a functor.
- `ModuleCat.representsLinearDual_self`: the case of `R` among `R`-modules.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The object `P` *represents the linear dual* of `Hom(P, X)`: every additive map
`f : Hom(P, X) ⟶ End P` which is `End P`-linear, `f (r ≫ x) = r ≫ f x`, is composition with a
unique morphism `φ : X ⟶ P`, that is `f x = x ≫ φ`. -/
def RepresentsLinearDual (P X : C) : Prop :=
  ∀ f : (P ⟶ X) → (P ⟶ P), (∀ x y, f (x + y) = f x + f y) → (∀ r x, f (r ≫ x) = r ≫ f x) →
    ∃! φ : X ⟶ P, ∀ x, x ≫ φ = f x

/-- `RepresentsLinearDual` is transported along a functor `F` which is bijective on the groups
`Hom(P, X)`, `End P` and `Hom(X, P)`, up to isomorphisms `F P ≅ P'` and `F X ≅ X'`. -/
lemma RepresentsLinearDual.of_functor {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] {P X : C} {P' X' : D} (eP : F.obj P ≅ P') (eX : F.obj X ≅ X')
    (h₁ : Function.Bijective (fun x : P ⟶ X ↦ F.map x))
    (h₂ : Function.Bijective (fun r : P ⟶ P ↦ F.map r))
    (h₃ : Function.Bijective (fun φ : X ⟶ P ↦ F.map φ))
    (h : RepresentsLinearDual P' X') : RepresentsLinearDual P X := by
  intro f hadd hlin
  -- the bijections `Hom(P, X) ≃ Hom(P', X')` and `End P ≃ End P'`
  let a : (P ⟶ X) ≃ (P' ⟶ X') :=
    (Equiv.ofBijective _ h₁).trans (eP.homCongr eX)
  let b : (P ⟶ P) ≃ (P' ⟶ P') :=
    (Equiv.ofBijective _ h₂).trans (eP.homCongr eP)
  have ha (x : P ⟶ X) : a x = eP.inv ≫ F.map x ≫ eX.hom := by simp [a, Iso.homCongr_apply]
  have hb (r : P ⟶ P) : b r = eP.inv ≫ F.map r ≫ eP.hom := by simp [b, Iso.homCongr_apply]
  have hab (r : P ⟶ P) (x : P ⟶ X) : a (r ≫ x) = b r ≫ a x := by simp [ha, hb]
  have hb' (r s : P ⟶ P) : b (r ≫ s) = b r ≫ b s := by simp [hb]
  have hadda (x y : P ⟶ X) : a (x + y) = a x + a y := by simp [ha]
  have haddb (r s : P ⟶ P) : b (r + s) = b r + b s := by simp [hb]
  let f' : (P' ⟶ X') → (P' ⟶ P') := fun x' ↦ b (f (a.symm x'))
  have hf'add (x y : P' ⟶ X') : f' (x + y) = f' x + f' y := by
    simp only [f']
    obtain ⟨x, rfl⟩ := a.surjective x
    obtain ⟨y, rfl⟩ := a.surjective y
    rw [← hadda, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hadd,
      haddb]
  have hf'lin (r : P' ⟶ P') (x : P' ⟶ X') : f' (r ≫ x) = r ≫ f' x := by
    simp only [f']
    obtain ⟨x, rfl⟩ := a.surjective x
    obtain ⟨r, rfl⟩ := b.surjective r
    rw [← hab, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hlin, hb']
  -- the bijection `Hom(X, P) ≃ Hom(X', P')`
  let c : (X ⟶ P) ≃ (X' ⟶ P') :=
    (Equiv.ofBijective _ h₃).trans (eX.homCongr eP)
  have hc (φ : X ⟶ P) : c φ = eX.inv ≫ F.map φ ≫ eP.hom := by simp [c, Iso.homCongr_apply]
  have hac (x : P ⟶ X) (φ : X ⟶ P) : b (x ≫ φ) = a x ≫ c φ := by simp [ha, hb, hc]
  obtain ⟨φ', hφ', huniq⟩ := h f' hf'add hf'lin
  obtain ⟨φ, rfl⟩ := c.surjective φ'
  refine ⟨φ, fun x ↦ b.injective ?_, fun ψ hψ ↦ c.injective (huniq _ fun x' ↦ ?_)⟩
  · rw [hac, hφ']
    simp only [f', Equiv.symm_apply_apply]
  · obtain ⟨x, rfl⟩ := a.surjective x'
    simp only [f', Equiv.symm_apply_apply]
    rw [← hψ, hac]

end CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- In the category of modules over a commutative ring `R`, the module `R` represents the
linear dual of `Hom_R(R, X) = X` for every module `X`: an additive `End R`-linear map
`Hom_R(R, X) ⟶ End R` is the same as a linear form `X ⟶ R`. -/
lemma representsLinearDual_self (X : ModuleCat.{u} R) :
    RepresentsLinearDual (ModuleCat.of R R) X := by
  intro f hadd hlin
  let s : X → (ModuleCat.of R R ⟶ X) := fun m ↦ ofHom (LinearMap.toSpanSingleton R X m)
  have hs (x : ModuleCat.of R R ⟶ X) : s (x.hom 1) = x := by
    ext
    simp [s]
  have hsadd (m m' : X) : s (m + m') = s m + s m' := by
    ext
    simp [s]
  let mul : R → (ModuleCat.of R R ⟶ ModuleCat.of R R) := fun c ↦ ofHom (c • LinearMap.id)
  have hsmul (c : R) (m : X) : s (c • m) = mul c ≫ s m := by
    ext
    simp [s, mul]
  let φ : X ⟶ ModuleCat.of R R := ofHom
    { toFun := fun m ↦ (f (s m)).hom 1
      map_add' := fun m m' ↦ by
        rw [hsadd, hadd]
        rfl
      map_smul' := fun c m ↦ by
        rw [hsmul, hlin]
        have := (f (s m)).hom.map_smul c 1
        simpa [mul] using this }
  refine ⟨φ, fun x ↦ ?_, fun ψ hψ ↦ ?_⟩
  · ext
    simp [φ, hs]
  · ext m
    have := congrArg (fun g : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ g.hom 1) (hψ (s m))
    simpa [φ, s] using this

end ModuleCat
