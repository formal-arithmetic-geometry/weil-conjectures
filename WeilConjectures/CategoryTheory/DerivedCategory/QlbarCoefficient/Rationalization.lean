/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.Module

/-!
# Rationalization of a linear category

Let `C` be an `R`-linear preadditive category and `M` a submonoid of `R`. The
*rationalization* `Rationalization M C` has the same objects as `C` and Hom groups the
localized modules `(X ⟶ Y)[M⁻¹]`. Equivalently it is obtained from `C` by inverting the
morphisms `m • 𝟙 X`, `m ∈ M`.

This is the passage from `Dᵇ_c(Y, 𝒪_E)` to `Dᵇ_c(Y, E)`. The morphisms that get inverted
are specified by a submonoid of the coefficient ring, so **no uniformizer is involved**:
one takes `M = Submonoid.powers ℓ` and simply inverts the fixed prime `ℓ`, using
`𝒪_E[1/ℓ] = E`, which holds because `ℓ` differs from a power of a uniformizer by a unit.
The reference notes instead write `Dᵇ_c(Y, 𝒪_E)[1/ϖ_E]`, which depends on the choice of a
uniformizer `ϖ_E`.

Whenever `A` is a localization of `R` at `M` — for instance `A = E` itself, viewed inside
`ℚ̄_ℓ` — the Hom groups are `A`-modules and the rationalization is `A`-linear.

## Main definitions

- `CategoryTheory.Rationalization`: the objects of the rationalized category.
- `CategoryTheory.Rationalization.homMk`: the morphism `f / m`.
- `CategoryTheory.Rationalization.category`, `preadditive`, `linear`.
- `CategoryTheory.Rationalization.toRationalization`: the canonical functor from `C`.
-/

@[expose] public section

universe uA uR v u

namespace CategoryTheory

open Category

variable {R : Type uR} [CommRing R]

/-- The rationalization of an `R`-linear category at a submonoid `M` of `R`: the objects
are those of `C`, and the morphisms are the localizations `(X ⟶ Y)[M⁻¹]`. -/
structure Rationalization (M : Submonoid R) (C : Type u) [Category.{v} C] [Preadditive C]
    [Linear R C] where
  /-- The underlying object of `C`. -/
  as : C

namespace Rationalization

variable {M : Submonoid R} {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

section Comp

variable {X Y Z : Rationalization M C}

/-- Composition of morphisms of the rationalization: `(f / m) ≫ (g / n) = (f ≫ g) / (m n)`. -/
noncomputable def comp (x : LocalizedModule M (X.as ⟶ Y.as))
    (y : LocalizedModule M (Y.as ⟶ Z.as)) : LocalizedModule M (X.as ⟶ Z.as) :=
  LocalizedModule.liftOn x
    (fun p ↦ LocalizedModule.liftOn y
      (fun q ↦ LocalizedModule.mk (p.1 ≫ q.1) (p.2 * q.2))
      (fun q q' hq ↦ by
        obtain ⟨u, hu⟩ := hq
        refine LocalizedModule.mk_eq.mpr ⟨u, ?_⟩
        simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, ← Linear.comp_smul] at hu ⊢
        have h := congrArg (fun z : Y.as ⟶ Z.as ↦ (p.2 : R) • z) hu
        simp only [smul_smul] at h
        congr 1
        rw [show (u : R) * ((p.2 : R) * (q'.2 : R)) = (p.2 : R) * ((u : R) * (q'.2 : R)) by ring,
          show (u : R) * ((p.2 : R) * (q.2 : R)) = (p.2 : R) * ((u : R) * (q.2 : R)) by ring]
        exact h))
    (fun p p' hp ↦ by
      obtain ⟨u, hu⟩ := hp
      induction y using LocalizedModule.induction_on with | h g n
      simp only [LocalizedModule.liftOn_mk]
      refine LocalizedModule.mk_eq.mpr ⟨u, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_smul, ← Linear.smul_comp] at hu ⊢
      have h := congrArg (fun z : X.as ⟶ Y.as ↦ (n : R) • z) hu
      simp only [smul_smul] at h
      congr 1
      rw [show (u : R) * ((p'.2 : R) * (n : R)) = (n : R) * ((u : R) * (p'.2 : R)) by ring,
        show (u : R) * ((p.2 : R) * (n : R)) = (n : R) * ((u : R) * (p.2 : R)) by ring]
      exact h)

lemma comp_mk (f : X.as ⟶ Y.as) (m : M) (g : Y.as ⟶ Z.as) (n : M) :
    comp (LocalizedModule.mk f m) (LocalizedModule.mk g n) =
      LocalizedModule.mk (f ≫ g) (m * n) := by
  simp only [comp, LocalizedModule.liftOn_mk]

end Comp

noncomputable instance category : Category (Rationalization M C) where
  Hom X Y := LocalizedModule M (X.as ⟶ Y.as)
  id X := LocalizedModule.mk (𝟙 X.as) 1
  comp := comp
  id_comp {X Y} x := by
    induction x using LocalizedModule.induction_on with | h f m
    change comp (LocalizedModule.mk (𝟙 X.as) 1) _ = _
    rw [comp_mk]
    simp
  comp_id {X Y} x := by
    induction x using LocalizedModule.induction_on with | h f m
    change comp _ (LocalizedModule.mk (𝟙 Y.as) 1) = _
    rw [comp_mk]
    simp
  assoc {X Y Z W} x y z := by
    induction x using LocalizedModule.induction_on with | h f m
    induction y using LocalizedModule.induction_on with | h g n
    induction z using LocalizedModule.induction_on with | h h' p
    change comp (comp _ _) _ = comp _ (comp _ _)
    rw [comp_mk, comp_mk, comp_mk, comp_mk, Category.assoc, mul_assoc]

/-- The morphism `f / m` of the rationalization. -/
abbrev homMk {X Y : Rationalization M C} (f : X.as ⟶ Y.as) (m : M) : X ⟶ Y :=
  LocalizedModule.mk f m

@[simp]
lemma homMk_comp_homMk {X Y Z : Rationalization M C} (f : X.as ⟶ Y.as) (m : M)
    (g : Y.as ⟶ Z.as) (n : M) : homMk f m ≫ homMk g n = homMk (f ≫ g) (m * n) :=
  comp_mk f m g n

@[simp]
lemma id_eq (X : Rationalization M C) : 𝟙 X = homMk (𝟙 X.as) 1 := rfl

lemma homMk_eq_homMk_iff {X Y : Rationalization M C} (f f' : X.as ⟶ Y.as) (m m' : M) :
    homMk f m = homMk f' m' ↔ ∃ u : M, u • m' • f = u • m • f' :=
  LocalizedModule.mk_eq

/-- Every morphism of the rationalization is of the form `f / m`. -/
@[elab_as_elim]
lemma homMk_induction {X Y : Rationalization M C} {P : (X ⟶ Y) → Prop}
    (h : ∀ (f : X.as ⟶ Y.as) (m : M), P (homMk f m)) (x : X ⟶ Y) : P x :=
  LocalizedModule.induction_on h x

noncomputable instance homAddCommGroup (X Y : Rationalization M C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (LocalizedModule M (X.as ⟶ Y.as)))

@[simp]
lemma homMk_add_homMk {X Y : Rationalization M C} (f f' : X.as ⟶ Y.as) (m m' : M) :
    homMk f m + homMk f' m' = homMk (m' • f + m • f') (m * m') :=
  LocalizedModule.mk_add_mk

noncomputable instance preadditive : Preadditive (Rationalization M C) where
  homGroup := homAddCommGroup
  add_comp P Q S' x x' y := by
    induction x using homMk_induction with | _ f m
    induction x' using homMk_induction with | _ f' m'
    induction y using homMk_induction with | _ g n
    rw [homMk_add_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_comp_homMk,
      homMk_add_homMk]
    simp only [Preadditive.add_comp, Submonoid.smul_def, Linear.smul_comp]
    refine (homMk_eq_homMk_iff _ _ _ _).2 ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_add, smul_smul]
    module
  comp_add P Q S' x y y' := by
    induction x using homMk_induction with | _ f m
    induction y using homMk_induction with | _ g n
    induction y' using homMk_induction with | _ g' n'
    rw [homMk_add_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_comp_homMk,
      homMk_add_homMk]
    simp only [Preadditive.comp_add, Submonoid.smul_def, Linear.comp_smul]
    refine (homMk_eq_homMk_iff _ _ _ _).2 ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Submonoid.coe_mul, one_smul, smul_add, smul_smul]
    module

/-- The canonical functor from `C` to its rationalization. -/
@[simps]
noncomputable def toRationalization : C ⥤ Rationalization M C where
  obj X := ⟨X⟩
  map f := homMk f 1
  map_id X := rfl
  map_comp f g := by rw [homMk_comp_homMk, mul_one]

instance : (toRationalization (M := M) (C := C)).Additive where
  map_add {X Y f g} := by
    simp only [toRationalization_map, homMk_add_homMk, mul_one]
    refine ((homMk_eq_homMk_iff _ _ _ _).2 ⟨1, ?_⟩).symm
    simp only [one_smul, smul_add]

section Linear

variable (A : Type uA) [CommRing A] [Algebra R A] [IsLocalization M A]

/-- If `A` is a localization of `R` at `M` -- for instance `A = E` and `M` the powers of
`ℓ` inside `𝒪_E` -- then the rationalization is `A`-linear. -/
noncomputable instance linear : Linear A (Rationalization M C) where
  homModule _ _ := LocalizedModule.moduleOfIsLocalization (T := A)
  smul_comp X Y Z a x y := by
    induction x using homMk_induction with | _ f m
    induction y using homMk_induction with | _ g n
    obtain ⟨r, s, rfl⟩ : ∃ (r : R) (s : M), a = IsLocalization.mk' A r s :=
      ⟨_, _, (IsLocalization.mk'_sec A a).symm⟩
    rw [LocalizedModule.mk'_smul_mk, homMk_comp_homMk, homMk_comp_homMk,
      LocalizedModule.mk'_smul_mk, Linear.smul_comp, ← mul_assoc]
  comp_smul X Y Z x a y := by
    induction x using homMk_induction with | _ f m
    induction y using homMk_induction with | _ g n
    obtain ⟨r, s, rfl⟩ : ∃ (r : R) (s : M), a = IsLocalization.mk' A r s :=
      ⟨_, _, (IsLocalization.mk'_sec A a).symm⟩
    rw [LocalizedModule.mk'_smul_mk, homMk_comp_homMk, homMk_comp_homMk,
      LocalizedModule.mk'_smul_mk, Linear.comp_smul, mul_left_comm m s n]

end Linear

end Rationalization

end CategoryTheory
