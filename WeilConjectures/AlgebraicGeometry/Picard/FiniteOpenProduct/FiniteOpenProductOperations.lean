/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients

/-! # Canonical finite open product operations

Source: Stacks 0GL1, and the open-product part of blueprint main-20261015,
sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md.
(blueprint: lem-pur-finite-open-product-swap).

We use the fixed-scalar presentation `FiniteD` of the ordinary constant-coefficient
module derived category, with its canonical intrinsic realization from the open
normalization dependency. Exact inverse image is localized termwise and identified
with its K-flat left derived functor. Tensor and symmetry are the K-flat ones.

## Main definitions and statement

- `comparison` and `comparisonOp`: the two specified factorization chains.
- `transportedReverse`: the reversed construction transported by the actual swaps.
- `restrictionSource`: the identification supplied by the two specified open units.
The theorem about these operations is in `FiniteOpenProductSwap`.

`product` names Mathlib's chosen pullback without unfolding its construction during
kernel checking. Its two projections and swap are the existing Mathlib morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace WeilConjectures.FiniteOpenProduct

/-- The chosen fibre-product object, kept named while deriving its operations.
Source: Mathlib pullback (blueprint: lem-pur-finite-open-product-swap). -/
@[irreducible]
def product {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : Scheme.{u} :=
  pullback a b

/-- First projection of the chosen product.
Source: Mathlib pullback (blueprint: lem-pur-finite-open-product-swap). -/
def first {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : product a b ⟶ T := by
  unfold product
  exact pullback.fst a b

/-- Second projection of the chosen product.
Source: Mathlib pullback (blueprint: lem-pur-finite-open-product-swap). -/
def second {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : product a b ⟶ U := by
  unfold product
  exact pullback.snd a b

/-- The actual swap of the two chosen fibre products.
Source: Mathlib pullbackSymmetry (blueprint: lem-pur-finite-open-product-swap). -/
def swap {T U B : Scheme.{u}} (a : T ⟶ B) (b : U ⟶ B) : product a b ≅ product b a := by
  unfold product
  exact pullbackSymmetry a b

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Exact inverse image on complexes, with its canonical K-flat derived identification.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : FiniteD A Y ⥤ FiniteD A X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- Composition for exact pullback, induced termwise before localization.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def pullComp {T U X : Scheme.{u}} (i : T ⟶ U) (j : U ⟶ X) :
    pull A (i ≫ j) ≅ pull A j ⋙ pull A i :=
  Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp (ModuleCat.{u + 1} A) i j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Geometric equality induces equality of the exact pullback functors.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def pullCongr {T X : Scheme.{u}} {f g : T ⟶ X} (w : f = g) : pull A f ≅ pull A g :=
  w ▸ Iso.refl _

/-- Canonical pullback composition along an equality of geometric composites.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def square {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (w : f ≫ g = h ≫ i) :
    pull A g ⋙ pull A f ≅ pull A i ⋙ pull A h :=
  (pullComp A f g).symm ≪≫
    pullCongr A w ≪≫
      pullComp A h i

variable {Xb Zb B X Z : Scheme.{u}}

/-- The first open on a product, formed by the chosen fibre-product functor.
Source: node proof Step 1 (blueprint: lem-pur-finite-open-product-swap). -/
def leftOpen (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) :
    product (j ≫ a) b ⟶ product a b := by
  unfold product
  exact pullback.map (j ≫ a) b a b j (𝟙 Zb) (𝟙 B) (by simp) (by simp)

/-- The second open on a product, formed by the same fibre-product functor.
Source: node proof Step 1 (blueprint: lem-pur-finite-open-product-swap). -/
def rightOpen (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb) :
    product a (k ≫ b) ⟶ product a b := by
  unfold product
  exact pullback.map a (k ≫ b) a b (𝟙 Xb) k (𝟙 B) (by simp) (by simp)

set_option linter.defProp false in
/-- Product base change for the first open, with its two projection equations.
Source: node proof Step 1 (blueprint: lem-pur-finite-open-product-swap). -/
def leftSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) :
    IsPullback (first (j ≫ a) b) (leftOpen a b j) j (first a b) := by
  unfold first leftOpen product
  dsimp only [id_eq]
  have h : IsPullback
      (pullback.map (j ≫ a) b a b j (𝟙 Zb) (𝟙 B) (by simp) (by simp) ≫
        pullback.snd a b) (pullback.fst (j ≫ a) b) b (j ≫ a) := by
    simpa using (IsPullback.of_hasPullback (j ≫ a) b).flip
  exact (h.of_right (by simp) (IsPullback.of_hasPullback a b).flip).flip

set_option linter.defProp false in
/-- Product base change for the second open.
Source: node proof Step 1 (blueprint: lem-pur-finite-open-product-swap). -/
def rightSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb) :
    IsPullback (second a (k ≫ b)) (rightOpen a b k) k (second a b) := by
  unfold second rightOpen product
  dsimp only [id_eq]
  have h : IsPullback
      (pullback.map a (k ≫ b) a b (𝟙 Xb) k (𝟙 B) (by simp) (by simp) ≫
        pullback.fst a b) (pullback.snd a (k ≫ b)) a (k ≫ b) := by
    simpa using (IsPullback.of_hasPullback a (k ≫ b))
  exact (h.of_right (by simp) (IsPullback.of_hasPullback a b)).flip

set_option linter.defProp false in
end WeilConjectures.FiniteOpenProduct
