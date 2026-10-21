/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.SixFunctors.OpenTensorNormalization
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Mathlib.AlgebraicGeometry.Pullbacks

import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Finite open external products and signed factor swap

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
- `finiteOpenProductSwap`: invertibility, restriction, equality and the signed swap equation.

`product` names Mathlib's chosen pullback without unfolding its construction during
kernel checking. Its two projections and swap are the existing Mathlib morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
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

/-- Evaluate the canonical K-flat Koszul braiding on a pro-etale coefficient category.
Source: signed tensor conventions (blueprint: lem-pur-finite-open-product-swap). -/
def proetSigma (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalClosed V]
    [MonoidalPreadditive V] [SymmetricCategory V] [Abelian.HasFunctorialFlatResolution V]
    (Y : Scheme.{u}) (M N : DerivedCategory (Sheaf (ProEt.topology Y) V)) :
    ((ProEtale.derivedTensor V Y).obj M).obj N ⟶
      ((ProEtale.derivedTensor V Y).obj N).obj M :=
  let μ := Functor.LaxMonoidal.μNatTrans
    (DerivedCategory.Qh (C := Sheaf (ProEt.topology Y) V))
  let W := HomotopyCategory.quasiIso (Sheaf (ProEt.topology Y) V) (.up ℤ)
  let τ := (ProEtale.derivedTensor V Y).leftDerived₂Lift μ W W
    (ProEtale.derivedTensor V Y).flip
    ((flipFunctor _ _ _).map μ ≫
      Functor.whiskerRight ((flipFunctor _ _ _).map
        (BraidedCategory.curriedBraidingNatIso
          (HomotopyCategory (Sheaf (ProEt.topology Y) V) (.up ℤ))).hom)
        ((Functor.whiskeringRight
          (HomotopyCategory (Sheaf (ProEt.topology Y) V) (.up ℤ))
          (HomotopyCategory (Sheaf (ProEt.topology Y) V) (.up ℤ))
          (DerivedCategory (Sheaf (ProEt.topology Y) V))).obj DerivedCategory.Qh))
  (τ.app N).app M

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The published derived tensor, with its coefficient specialization named.
Source: Stacks 06YS (blueprint: lem-pur-finite-open-product-swap). -/
abbrev tensor (Y : Scheme.{u}) (M N : FiniteD A Y) : FiniteD A Y :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M).obj N

/-- Map both arguments of the published derived tensor bifunctor.
Source: Stacks 06YS (blueprint: lem-pur-finite-open-product-swap). -/
def tensorMap (Y : Scheme.{u}) {M M' N N' : FiniteD A Y}
    (f : M ⟶ M') (g : N ⟶ N') : tensor A Y M N ⟶ tensor A Y M' N' :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).map f).app N ≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M').map g

/-- Map two isomorphisms under the same published derived tensor bifunctor.
Source: Stacks 06YS (blueprint: lem-pur-finite-open-product-swap). -/
def tensorIsoMap (Y : Scheme.{u}) {M M' N N' : FiniteD A Y}
    (f : M ≅ M') (g : N ≅ N') : tensor A Y M N ≅ tensor A Y M' N' :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).mapIso f).app N ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M').mapIso g

/-- Exact inverse image on complexes, with its canonical K-flat derived identification.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : FiniteD A Y ⥤ FiniteD A X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- The finite ring is Noetherian; this supplies the published flat-pullback API.
Source: finite coefficient conventions (blueprint: lem-pur-finite-open-product-swap). -/
instance coefficientNoetherian : IsNoetherianRing A := isNoetherian_of_finite A A

/-- Tensor comparison for exact inverse image, with its canonical derived identification.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def tensorPullIso {T U : Scheme.{u}} (f : T ⟶ U) (M N : FiniteD A U) :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) f).symm.app (tensor A U M N) ≪≫
    ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f M N ≪≫
      tensorIsoMap A T
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).app M)
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).app N)

/-- The open adjunction, using the canonical exact/left-derived identification.
Source: Stacks 03DI (blueprint: lem-pur-finite-open-product-swap). -/
def adj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    finiteShriek A j ⊣ pull A j :=
  ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j

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

/-- Unit-compatible composition of exact open extensions, descended termwise.
Source: Stacks 03DI; the canonical open compositor
(blueprint: lem-pur-finite-open-product-swap). -/
def comp {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    finiteShriek A i ⋙ finiteShriek A j ≅ finiteShriek A (i ≫ j) :=
  (((adj A i).comp (adj A j)).ofNatIsoRight
    (pullComp A i j).symm).leftAdjointUniq
      (adj A (i ≫ j))

/-- Canonical pullback composition along an equality of geometric composites.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def square {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Z)
    (h : T ⟶ Y) (i : Y ⟶ Z) (w : f ≫ g = h ≫ i) :
    pull A g ⋙ pull A f ≅ pull A i ⋙ pull A h :=
  (pullComp A f g).symm ≪≫
    pullCongr A w ≪≫
      pullComp A h i

/-- Compose the canonical pullback comparison with a geometric projection equality.
Source: Stacks 07A4 (blueprint: lem-pur-finite-open-product-swap). -/
def composeEq {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : T ⟶ Y) (w : f ≫ g = h) : pull A g ⋙ pull A f ≅ pull A h :=
  (pullComp A f g).symm ≪≫
    pullCongr A w

/-- Open base change with the exact/left-derived comparisons made explicit.
Its inverse is the normalized open-unit mate, as in the normalization dependency.
Source: Stacks 03S6 (blueprint: lem-pur-finite-open-product-swap). -/
def beta {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback gU j' j g) :
    finiteShriek A j ⋙ pull A g ≅ pull A gU ⋙ finiteShriek A j' :=
  ProEtale.ordinaryOpenExtensionBaseChangeIso A gU j' j g s

/-- The actual normalized open tensor comparison, in extension-first order.
Source: Stacks 0GL1 (blueprint: lem-pur-finite-open-product-swap). -/
def gamma {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A U) (N : FiniteD A X) :=
  finiteGamma A j M N ≫
    (finiteShriek A j).map
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) U).obj M).map
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) j).hom.app N))

/-- The canonical Koszul braiding descended from the homotopy category.
Source: signed tensor conventions (blueprint: lem-pur-finite-open-product-swap). -/
def sigma (Y : Scheme.{u}) (M N : FiniteD A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj M).obj N ⟶
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj N).obj M :=
  proetSigma (ModuleCat.{u + 1} A) Y M N

/-- Right-extension order uses both signed symmetries, rather than an unsigned flip.
Source: node proof Step 3; Stacks 0GL1
(blueprint: lem-pur-finite-open-product-swap). -/
def rho {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : FiniteD A X) (N : FiniteD A U) :=
  sigma A _ M ((finiteShriek A j).obj N) ≫ gamma A j N M ≫
    (finiteShriek A j).map (sigma A _ N ((pull A j).obj M))

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

/-- Openness of the first factor inclusion is the base-change instance.
Source: Stacks 01JY (blueprint: lem-pur-finite-open-product-swap). -/
instance leftOpen_open (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb)
    [IsOpenImmersion j] : IsOpenImmersion (leftOpen a b j) := by
  unfold leftOpen product
  dsimp only [id_eq]
  infer_instance

/-- Openness of the second factor inclusion is the base-change instance.
Source: Stacks 01JY (blueprint: lem-pur-finite-open-product-swap). -/
instance rightOpen_open (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb)
    [IsOpenImmersion k] : IsOpenImmersion (rightOpen a b k) := by
  unfold rightOpen product
  dsimp only [id_eq]
  infer_instance

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

/-- The first base-change step, tensored with the untouched second pullback.
Source: node proof Step 4 (blueprint: lem-pur-finite-open-product-swap). -/
def leftBeta (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb)
    [IsOpenImmersion j] (M : FiniteD A X) (N : FiniteD A Zb) :=
  tensorMap A (product a b) ((beta A _ _ _ _ (leftSquare a b j)).hom.app M)
    (𝟙 ((pull A (second a b)).obj N))

/-- Tensor the projection-composition comparison at an abstract geometric corner.
Source: node proof Step 4 (blueprint: lem-pur-finite-open-product-swap). -/
def projectionTensor {V C T U : Scheme.{u}} (v : V ⟶ C) (t : C ⟶ T)
    (p : V ⟶ U) (q : V ⟶ T) (h : v ≫ t = q)
    (M : FiniteD A U) (N : FiniteD A T) :
    tensor A V ((pull A p).obj M) ((pull A v).obj ((pull A t).obj N)) ⟶
      tensor A V ((pull A p).obj M) ((pull A q).obj N) :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj ((pull A p).obj M)).map
    ((composeEq A v t q h).hom.app N)

/-- Extend the projection-tensor comparison at the same abstract corner.
Source: node proof Step 4 (blueprint: lem-pur-finite-open-product-swap). -/
def extendedProjectionTensor {V C T U : Scheme.{u}} (v : V ⟶ C) [IsOpenImmersion v]
    (t : C ⟶ T) (p : V ⟶ U) (q : V ⟶ T) (h : v ≫ t = q)
    (M : FiniteD A U) (N : FiniteD A T) :
    (finiteShriek A v).obj
      (tensor A V ((pull A p).obj M) ((pull A v).obj ((pull A t).obj N))) ⟶
    (finiteShriek A v).obj (tensor A V ((pull A p).obj M) ((pull A q).obj N)) :=
  (finiteShriek A v).map (projectionTensor A v t p q h M N)

/-- The specified first-factor comparison, beta followed by gamma and projections.
Source: node proof Step 4 (blueprint: lem-pur-finite-open-product-swap). -/
def leftComparison (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb)
    [IsOpenImmersion j] (M : FiniteD A X) (N : FiniteD A Zb) :=
  leftBeta A a b j M N ≫
    gamma A (leftOpen a b j) ((pull A (first (j ≫ a) b)).obj M)
      ((pull A (second a b)).obj N) ≫ extendedProjectionTensor A (leftOpen a b j) (second a b)
        (first (j ≫ a) b) (second (j ≫ a) b) (by
          unfold leftOpen second product
          dsimp only [id_eq]
          simp) M N

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

/-- The one-factor comparison with the extension in the right factor.
The rho composite includes its two Koszul symmetries explicitly.
Source: node proof Steps 3 and 6 (blueprint: lem-pur-finite-open-product-swap). -/
def rightComparison (a : Xb ⟶ B) (b : Zb ⟶ B) (k : Z ⟶ Zb)
    [IsOpenImmersion k] (M : FiniteD A Xb) (N : FiniteD A Z) :=
  tensorMap A (product a b) (𝟙 ((pull A (first a b)).obj M))
      ((beta A _ _ _ _ (rightSquare a b k)).hom.app N) ≫
    rho A (rightOpen a b k) ((pull A (first a b)).obj M)
      ((pull A (second a (k ≫ b))).obj N) ≫
      (finiteShriek A (rightOpen a b k)).map
        (tensorMap A _ ((composeEq A (rightOpen a b k) (first a b)
          (first a (k ≫ b)) (by
            unfold rightOpen first product
            dsimp only [id_eq]
            simp)).hom.app M)
          (𝟙 ((pull A (second a (k ≫ b))).obj N)))

/-- The actual product open immersion u=j times k, on the chosen fibre products.
Source: node statement and proof Step 1 (blueprint: lem-pur-finite-open-product-swap). -/
def productOpen (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb) :
    product (j ≫ a) (k ≫ b) ⟶ product a b := by
  unfold product
  exact pullback.map (j ≫ a) (k ≫ b) a b j k (𝟙 B) (by simp) (by simp)

/-- The product map is open by the existing base-change instance.
Source: Stacks 01JY (blueprint: lem-pur-finite-open-product-swap). -/
instance productOpen_open (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] : IsOpenImmersion (productOpen a b j k) := by
  unfold productOpen product
  dsimp only [id_eq]
  infer_instance

/-- The canonical compositor, followed only by a geometric equality of open maps.
Source: node proof Step 2 (blueprint: lem-pur-finite-open-product-swap). -/
def compTo {T U Y : Scheme.{u}} (i : T ⟶ U) (j : U ⟶ Y) (h : T ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion h] (w : i ≫ j = h) :
    finiteShriek A i ⋙ finiteShriek A j ≅ finiteShriek A h :=
  comp A i j ≪≫ (by
    subst h
    exact Iso.refl _)

/-- The specified first-factor-then-second-factor external product map e.
Every factor is the actual normalized beta, gamma, signed rho or open compositor.
Source: node proof Step 4 (blueprint: lem-pur-finite-open-product-swap). -/
def comparison (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :=
  leftComparison A a b j M ((finiteShriek A k).obj N) ≫
    (finiteShriek A (leftOpen a b j)).map (rightComparison A (j ≫ a) b k M N) ≫
      (compTo A (rightOpen (j ≫ a) b k) (leftOpen a b j) (productOpen a b j k)
        (by
          unfold rightOpen leftOpen productOpen product
          dsimp only [id_eq]
          apply pullback.hom_ext <;> simp)).hom.app _

/-- The other factorization, through Xbar times Z, defines e-op independently.
Source: node proof Step 6 (blueprint: lem-pur-finite-open-product-swap). -/
def comparisonOp (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :=
  rightComparison A a b k ((finiteShriek A j).obj M) N ≫
    (finiteShriek A (rightOpen a b k)).map (leftComparison A a (k ≫ b) j M N) ≫
      (compTo A (leftOpen a (k ≫ b) j) (rightOpen a b k) (productOpen a b j k)
        (by
          unfold rightOpen leftOpen productOpen product
          dsimp only [id_eq]
          apply pullback.hom_ext <;> simp)).hom.app _

/-- Pulling the reversed external tensor along the actual fibre-product swap.
There is no symmetry in this identification: the reversed factors stay reversed.
Source: node proof Step 8 (blueprint: lem-pur-finite-open-product-swap). -/
def swapFactors (a : Xb ⟶ B) (b : Zb ⟶ B)
    (M : FiniteD A Xb) (N : FiniteD A Zb) :=
  tensorPullIso A _ _ _ ≪≫
    tensorIsoMap A _
      ((composeEq A (swap a b).hom (first b a)
        (second a b) (by
          unfold swap first second product
          dsimp only [id_eq]
          simp)).app N)
      ((composeEq A (swap a b).hom (second b a)
        (first a b) (by
          unfold swap first second product
          dsimp only [id_eq]
          simp)).app M)

set_option linter.defProp false in
/-- The Cartesian square between the two actual product opens under factor swap.
Source: node proof Step 8 (blueprint: lem-pur-finite-open-product-swap). -/
def swapSquare (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb) :
    IsPullback (swap (j ≫ a) (k ≫ b)).hom
      (productOpen a b j k) (productOpen b a k j) (swap a b).hom :=
  IsPullback.of_horiz_isIso ⟨by
    unfold swap productOpen product
    dsimp only [id_eq]
    apply pullback.hom_ext <;> simp⟩

/-- The reversed construction pulled back by the ambient swap, followed by the
normalized open base change and the projection/tensor identifications.
Source: node proof Step 8 (blueprint: lem-pur-finite-open-product-swap). -/
def transportedReverse (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :=
  (swapFactors A a b ((finiteShriek A j).obj M) ((finiteShriek A k).obj N)).inv ≫
    (pull A (swap a b).hom).map (comparison A b a k j N M) ≫
      (beta A _ _ _ _ (swapSquare a b j k)).hom.app _ ≫
        (finiteShriek A (productOpen a b j k)).map
          (swapFactors A (j ≫ a) (k ≫ b) M N).hom

/-- Identify D with the restriction of the ambient external product using exactly
both open units and the canonical pullback/tensor identifications. Written in the
forward direction so the restriction identity is its unit equation.
Source: node proof Step 5 (blueprint: lem-pur-finite-open-product-swap). -/
def restrictionSource (a : Xb ⟶ B) (b : Zb ⟶ B) (j : X ⟶ Xb) (k : Z ⟶ Zb)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : FiniteD A X) (N : FiniteD A Z) :=
  tensorMap A _
    ((pull A (first (j ≫ a) (k ≫ b))).map ((adj A j).unit.app M) ≫
      (square A (productOpen a b j k) (first a b)
        (first (j ≫ a) (k ≫ b)) j (by
          unfold productOpen first product
          dsimp only [id_eq]
          simp)).inv.app _)
    ((pull A (second (j ≫ a) (k ≫ b))).map ((adj A k).unit.app N) ≫
      (square A (productOpen a b j k) (second a b)
        (second (j ≫ a) (k ≫ b)) k (by
          unfold productOpen second product
          dsimp only [id_eq]
          simp)).inv.app _) ≫
    (tensorPullIso A (productOpen a b j k) _ _).inv

/-- Finiteness of the recorded coefficient ring, with its standard size lift.
Source: finite purity conventions (blueprint: lem-pur-finite-open-product-swap). -/
instance settingCoefficientFinite (S : PurityFiniteSetting.{u}) : Finite S.Coefficient :=
  letI : Finite S.Ring := Padic.finite_coefficientExtensionRing
    S.coefficients.l S.extension S.level S.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} S.Ring))

/-- Both actual external-product maps are isomorphisms, restrict to the identity,
agree, and commute with the actual product swap and signed tensor symmetry.
Source: Stacks 0GL1 and the open-product signed-symmetry reduction in blueprint
main-20261015, lem-sf-kunneth-coherence.proof.md
(blueprint: lem-pur-finite-open-product-swap).

Proof: (1) The fibre-product projection equations give the four Cartesian squares;
base change makes all four factor inclusions open. (2) The compositor is the unique
mate of restriction composition. Its unit is the composite of the two open units,
so its restriction is identity. (3) The right-extension tensor map is symmetry,
then gamma, then extension of symmetry. Its restriction is identity since the two
Koszul signs multiply to (-1)^(ab+ba)=1. (4) The definition of comparison is beta
for j, gamma for v, then inside v-shriek beta for k and rho for w, then the
compositor. All factors are invertible by openTensorNormalization. (5) Restricting
this chain gives identity at each stage; product/tensor composition coherence
identifies the result with the displayed unit equation. (6) comparisonOp uses the
other factorization: beta for k, rho for v-prime, then beta for j and gamma for
w-prime, and its compositor. Its restriction gives the same unit equation.
(7) To compare maps E to u-shriek D, compose with comparison inverse. Full
faithfulness of u-shriek and naturality of its invertible unit show that equal
restrictions imply equality. (8) Apply the construction with the two factors
interchanged and pull back by the actual two fibre-product symmetries. Normalized
base change identifies its restriction with identity on the reversed tensor.
(9) Conjugate with both signed symmetries. Their restrictions cancel, so Step 7
gives the final equation of actual maps. The cochain sign computation and K-flat
descent apply to arbitrary unbounded objects, including odd degrees. -/
theorem finiteOpenProductSwap (S : PurityFiniteSetting.{u})
    (Xb Zb B X Z : Over (Spec (CommRingCat.of S.field.k)))
    [IsSeparated Xb.hom] [LocallyOfFiniteType Xb.hom] [QuasiCompact Xb.hom]
    [IsSeparated Zb.hom] [LocallyOfFiniteType Zb.hom] [QuasiCompact Zb.hom]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (a : Xb ⟶ B) (b : Zb ⟶ B)
    [IsSeparated a.left] [LocallyOfFiniteType a.left] [QuasiCompact a.left]
    [IsSeparated b.left] [LocallyOfFiniteType b.left] [QuasiCompact b.left]
    (j : X ⟶ Xb) (k : Z ⟶ Zb) [IsOpenImmersion j.left] [IsOpenImmersion k.left]
    (M : FiniteD S.Coefficient X.left) (N : FiniteD S.Coefficient Z.left) :
    IsIso (comparison S.Coefficient a.left b.left j.left k.left M N) ∧
    IsIso (comparisonOp S.Coefficient a.left b.left j.left k.left M N) ∧
    (restrictionSource S.Coefficient a.left b.left j.left k.left M N ≫
      (pull S.Coefficient (productOpen a.left b.left j.left k.left)).map
        (comparison S.Coefficient a.left b.left j.left k.left M N) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) ∧
    (restrictionSource S.Coefficient a.left b.left j.left k.left M N ≫
      (pull S.Coefficient (productOpen a.left b.left j.left k.left)).map
        (comparisonOp S.Coefficient a.left b.left j.left k.left M N) =
      (adj S.Coefficient (productOpen a.left b.left j.left k.left)).unit.app
        (tensor S.Coefficient (product (j.left ≫ a.left) (k.left ≫ b.left))
          ((pull S.Coefficient (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)
          ((pull S.Coefficient (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N))) ∧
    comparison S.Coefficient a.left b.left j.left k.left M N =
      comparisonOp S.Coefficient a.left b.left j.left k.left M N ∧
    comparison S.Coefficient a.left b.left j.left k.left M N =
      sigma S.Coefficient _ _ _ ≫
        transportedReverse S.Coefficient a.left b.left j.left k.left M N ≫
          (finiteShriek S.Coefficient (productOpen a.left b.left j.left k.left)).map
            (sigma S.Coefficient _ ((pull S.Coefficient
                (second (j.left ≫ a.left) (k.left ≫ b.left))).obj N)
              ((pull S.Coefficient
                (first (j.left ≫ a.left) (k.left ≫ b.left))).obj M)) := by
  sorry

end WeilConjectures.FiniteOpenProduct
