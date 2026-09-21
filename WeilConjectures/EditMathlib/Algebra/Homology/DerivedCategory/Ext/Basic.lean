/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import WeilConjectures.EditMathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Localization.SmallShiftedHom

-- Ported from `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`,
-- with `DerivedCategory` replaced by the opaque wrapper `DerivedCategory'`.

/-!
# Ext groups in abelian categories

Let `C` be an abelian category (with `C : Type u` and `Category.{v} C`).
In this file, we introduce the assumption `HasExt.{w} C` which asserts
that morphisms between single complexes in arbitrary degrees in
the derived category of `C` are `w`-small. Under this assumption,
we define `Ext.{w} X Y n : Type w` as shrunk versions of suitable
types of morphisms in the derived category. In particular, when `C` has
enough projectives or enough injectives, the property `HasExt.{v} C`
shall hold.

Note: in certain situations, `w := v` shall be the preferred
choice of universe (e.g. if `C := ModuleCat.{v} R` with `R : Type v`).
However, in the development of the API for Ext-groups, it is important
to keep a larger degree of generality for universes, as `w < v`
may happen in certain situations. Indeed, if `X : Scheme.{u}`,
then the underlying category of the étale site of `X` shall be a large
category. However, the category `Sheaf X.Etale AddCommGrpCat.{u}`
shall have good properties (because there is a small category of affine
schemes with the same category of sheaves), and even though the type of
morphisms in `Sheaf X.Etale AddCommGrpCat.{u}` shall be
in `Type (u + 1)`, these types are going to be `u`-small.
Then, for `C := Sheaf X.etale AddCommGrpCat.{u}`, we will have
`Category.{u + 1} C`, but `HasExt.{u} C` will hold
(as `C` has enough injectives). Then, the `Ext` groups between étale
sheaves over `X` shall be in `Type u`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w'' w' w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits ZeroObject DerivedCategory' Pretriangulated

/-- The property that morphisms between single complexes in arbitrary degrees are `w`-small
in the derived category. -/
abbrev HasExt : Prop :=
  ∀ (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ) (_ : 0 ≤ n), Small.{w}
      ((singleFunctor C 0).obj X ⟶
        (((singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    obtain hab | hab := le_or_gt a b
    · refine (small_congr ?_).1 (h X Y (b - a) (by simpa))
      exact (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor _ a)).homEquiv.trans
        ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv
    · suffices Subsingleton ((Q.obj ((CochainComplex.singleFunctor C 0).obj X))⟦a⟧ ⟶
          (Q.obj ((CochainComplex.singleFunctor C 0).obj Y))⟦b⟧) from inferInstance
      constructor
      intro x y
      rw [← cancel_mono ((Q.commShiftIso b).inv.app _),
        ← cancel_epi ((Q.commShiftIso a).hom.app _)]
      have : (((CochainComplex.singleFunctor C 0).obj X)⟦a⟧).IsStrictlyLE (-a) :=
        CochainComplex.isStrictlyLE_shift _ 0 _ _ (by lia)
      have : (((CochainComplex.singleFunctor C 0).obj Y)⟦b⟧).IsStrictlyGE (-b) :=
        CochainComplex.isStrictlyGE_shift _ 0 _ _ (by lia)
      apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE _ _ (-a) (-b) (by
        lia)).elim

lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance

lemma HasExt.standard : HasExt.{max u v} C := by
  let := HasDerivedCategory.standard
  exact hasExt_of_hasDerivedCategory _

instance [HasExt.{w} C] (X Y : C) (a b : ℤ) [HasDerivedCategory.{w'} C] :
    Small.{w} ((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) := by
  have (a b : ℤ) :
      Small.{w} (((singleFunctor C 0).obj X)⟦a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦b⟧) :=
    (hasSmallLocalizedShiftedHom_iff.{w}
      (W := (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))) (M := ℤ)
      (X := (CochainComplex.singleFunctor C 0).obj X)
      (Y := (CochainComplex.singleFunctor C 0).obj Y) Q).1 inferInstance a b
  exact small_of_injective
    (β := ((singleFunctor C 0).obj X)⟦-a⟧ ⟶ ((singleFunctor C 0).obj Y)⟦-b⟧)
    (f := fun φ ↦
      ((singleFunctors C).shiftIso (-a) a 0 (by simp)).hom.app X ≫ φ ≫
        ((singleFunctors C).shiftIso (-b) b 0 (by simp)).inv.app Y)
    (fun φ₁ φ₂ h ↦ by simpa using h)

variable {C}

variable [HasExt.{w} C]

namespace Abelian

/-- An Ext-group in an abelian category `C`, defined as a `Type w` when `[HasExt.{w} C]`. -/
def Ext (X Y : C) (n : ℕ) : Type w :=
  SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)

namespace Ext

variable {X Y Z T : C}

/-- The composition of `Ext`. -/
noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    Ext X Z c :=
  SmallShiftedHom.comp α β (by lia)

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by lia) =
      α.comp (β.comp γ h₂₃) (by lia) :=
  SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by lia)

@[simp]
lemma comp_assoc_of_second_deg_zero
    {a₁ a₃ a₁₃ : ℕ} (α : Ext X Y a₁) (β : Ext Y Z 0) (γ : Ext Z T a₃)
    (h₁₃ : a₁ + a₃ = a₁₃) :
    (α.comp β (add_zero _)).comp γ h₁₃ = α.comp (β.comp γ (zero_add _)) h₁₃ := by
  apply comp_assoc
  lia

@[simp]
lemma comp_assoc_of_third_deg_zero
    {a₁ a₂ a₁₂ : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T 0)
    (h₁₂ : a₁ + a₂ = a₁₂) :
    (α.comp β h₁₂).comp γ (add_zero _) = α.comp (β.comp γ (add_zero _)) h₁₂ := by
  apply comp_assoc
  lia

section

variable [HasDerivedCategory.{w'} C]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the bijection
between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
noncomputable def homEquiv {n : ℕ} :
    Ext.{w} X Y n ≃ ShiftedHom ((singleFunctor C 0).obj X)
      ((singleFunctor C 0).obj Y) (n : ℤ) :=
  SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) Q

/-- The morphism in the derived category which corresponds to an element in `Ext X Y a`. -/
noncomputable abbrev hom {a : ℕ} (α : Ext X Y a) :
    ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (a : ℤ) :=
  homEquiv α

@[simp]
lemma comp_hom {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by lia) := by
  apply SmallShiftedHom.equiv_comp

@[ext]
lemma ext {n : ℕ} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
  homEquiv.injective h

end

/-- The canonical map `(X ⟶ Y) → Ext X Y 0`. -/
noncomputable def mk₀ (f : X ⟶ Y) : Ext X Y 0 := SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]
lemma mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map f) := by
  apply SmallShiftedHom.equiv_mk₀

@[simp]
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mk₀ f).comp (mk₀ g) (zero_add 0) = mk₀ (f ≫ g) := by
  let := HasDerivedCategory.standard C; ext; simp

@[simp]
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (α : Ext Z T n) :
    (mk₀ f).comp ((mk₀ g).comp α (zero_add n)) (zero_add n) =
      (mk₀ (f ≫ g)).comp α (zero_add n) := by
  rw [← mk₀_comp_mk₀, comp_assoc]
  lia

/-
OBSTRUCTION (`no_expose`).

The rest of `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean` is *not* ported. It is
blocked on two declarations whose mathlib proofs rely on the objects of the derived category
being a concrete quotient category — which is exactly what `DerivedCategory'` hides:

* `DerivedCategory.Ext.mk₀_bijective` (and hence `homEquiv₀`, `mk₀_homEquiv₀_apply`,
  `addEquiv₀`, `mk₀_addEquiv₀_apply`);
* `DerivedCategory.Ext.biprod_ext` (and hence `add_hom`, and with it the whole
  `AddCommGroup (Ext X Y n)` / `Module R (Ext X Y n)` API and everything below it).

In both cases the elaborator ends up unifying a metavariable of type
`HomotopyCategory C (ComplexShape.up ℤ)` (resp. `Discrete WalkingPair`) against a term of type
`DerivedCategory' C`. Since `DerivedCategory'` cannot be unfolded, that unification is not
refuted, and the resulting proof term contains a `Quotient.as` projection applied to an object
of `DerivedCategory' C`. Under mathlib's exposed `DerivedCategory` such a projection happens to
be well typed; here the kernel rejects it with `invalid projection`.

Consequently, none of the files under `Mathlib/Algebra/Homology/DerivedCategory/Ext/` other than
this fragment is ported, nor any of their downstream users
(`Mathlib/Algebra/Category/ModuleCat/Ext/*`, `Mathlib/CategoryTheory/Abelian/*/Ext.lean`,
`Mathlib/CategoryTheory/Sites/SheafCohomology/*`, …).
-/

end Ext

end CategoryTheory.Abelian
