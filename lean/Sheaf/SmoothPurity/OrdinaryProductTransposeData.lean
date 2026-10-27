/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteDirectImageComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteForwardProductSymmetry
public import Sheaf.Paper.FiniteProductCompactification

/-! # Data for ordinary external-product transposes

Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.proof.md, clauses (i)--(ii)
(blueprint: def-pur-ordinary-product-transpose-data).

The fixed-scalar presentation is the ordinary unbounded category of constant-A modules.
A cartesian product diagram chooses a common representative for both triple products;
its projection equations implement their canonical identification by the universal property.
Every comparison below is the published pullback, tensor, or direct-image compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

/-- Abbreviation for the ordinary constant-coefficient category, with the standard size lift.
Source: def-pur-conventions (blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryCategory (X : Scheme.{u}) :=
  DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))

/-- The existing K-flat pullback, without restricting its unbounded domain.
Source: def-weil-pbc-proetale-operations
(blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

/-- The existing K-injective direct image on the ordinary unbounded category.
Source: def-weil-pbc-proetale-operations
(blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor

/-- The existing derived adjunction, with its specified unit and counit.
Source: def-weil-pbc-proetale-operations
(blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f

/-- The specified pullback-tensor comparison, evaluated at two objects.
Source: Stacks 07A4 (blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : P.ordinaryCategory Y) :
    (P.ordinaryPull f).obj (K ⊗ L) ≅
      (P.ordinaryPull f).obj K ⊗ (P.ordinaryPull f).obj L :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f K L

/-- The specified pullback composition comparison.
Source: Stacks 07A4 (blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryPullComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g

/-- Transport the existing direct image along equality of scheme maps.
Source: canonical composition identifications in the blueprint's coherence proof
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryPushCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    P.ordinaryPush f ≅ P.ordinaryPush g :=
  h ▸ Iso.refl _

/-- The external product on a specified fibre-product cone.
Source: def-pc-fibre-product and the node's boxtimes formula
(blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryExternal {W X Y : Scheme.{u}} (r : W ⟶ X) (t : W ⟶ Y)
    (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y) :=
  (P.ordinaryPull r).obj K ⊗ (P.ordinaryPull t).obj L

/-- The actual ordinary product: two signed swaps, projection, exchange tensored with
identity, projection again, then the inverse specified direct-image compositor.
Its codomain uses w = t followed by v, the common structure map of the square.
Source: def-exchange-projection and the node's displayed Omega formula
(blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryProduct {W X Y B : Scheme.{u}} {r : W ⟶ X} {t : W ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback r t f g)
    (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y) :
    (P.ordinaryPush f).obj K ⊗ (P.ordinaryPush g).obj L ⟶
      (P.ordinaryPush (t ≫ g)).obj (P.ordinaryExternal r t K L) :=
  finiteProductOrdinary P.Coefficient f g sq K L

/-- Chosen double products and one common triple product, with its four cartesian cones.
The last two equations say that both cones have the same second and third projections;
the first projection is literally a followed by p1. These are precisely the canonical
identifications of the two parenthesized products, not extra geometric hypotheses.
Source: def-pc-fibre-product; blueprint coherence proof, associativity clause
(blueprint: def-pur-ordinary-product-transpose-data). -/
structure OrdinaryTripleProductDiagram {X₁ X₂ X₃ B : Scheme.{u}}
    (f₁ : X₁ ⟶ B) (f₂ : X₂ ⟶ B) (f₃ : X₃ ⟶ B) where
  X₁₂ : Scheme.{u}
  X₂₃ : Scheme.{u}
  T : Scheme.{u}
  p₁ : X₁₂ ⟶ X₁
  p₂ : X₁₂ ⟶ X₂
  q₂ : X₂₃ ⟶ X₂
  q₃ : X₂₃ ⟶ X₃
  a : T ⟶ X₁₂
  b : T ⟶ X₂₃
  c : T ⟶ X₃
  square₁₂ : IsPullback p₁ p₂ f₁ f₂
  square₂₃ : IsPullback q₂ q₃ f₂ f₃
  squareL : IsPullback a c (p₂ ≫ f₂) f₃
  squareR : IsPullback (a ≫ p₁) b f₁ (q₂ ≫ f₂)
  second : b ≫ q₂ = a ≫ p₂
  third : b ≫ q₃ = c

variable {X₁ X₂ X₃ B : Scheme.{u}} {f₁ : X₁ ⟶ B} {f₂ : X₂ ⟶ B} {f₃ : X₃ ⟶ B}
    (d : OrdinaryTripleProductDiagram f₁ f₂ f₃)
    (K : P.ordinaryCategory X₁) (L : P.ordinaryCategory X₂) (M : P.ordinaryCategory X₃)

/-- The common, left-associated triple external tensor, with its ordered projections.
Source: the node's common codomain (blueprint: def-pur-ordinary-product-transpose-data). -/
abbrev ordinaryTripleObject :=
  ((P.ordinaryPull (d.a ≫ d.p₁)).obj K ⊗ (P.ordinaryPull (d.a ≫ d.p₂)).obj L) ⊗
    (P.ordinaryPull d.c).obj M

/-- Canonical identification of the left iterated external tensor with the common tensor.
Source: Stacks 07A4, pullback and tensor composition
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryTripleLeftIdentification :
    P.ordinaryExternal d.a d.c (P.ordinaryExternal d.p₁ d.p₂ K L) M ≅
      P.ordinaryTripleObject d K L M :=
  tensorIso
    (P.ordinaryTensorComparison d.a _ _ ≪≫ tensorIso
      ((P.ordinaryPullComposition d.a d.p₁).symm.app K)
      ((P.ordinaryPullComposition d.a d.p₂).symm.app L)) (Iso.refl _)

/-- Canonical identification of the right iterated external tensor with the common tensor.
It retains the tensor associator and the equations identifying all three projections.
Source: Stacks 07A4; fibre-product associativity
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryTripleRightIdentification :
    P.ordinaryExternal (d.a ≫ d.p₁) d.b K (P.ordinaryExternal d.q₂ d.q₃ L M) ≅
      P.ordinaryTripleObject d K L M :=
  tensorIso (Iso.refl _)
    (P.ordinaryTensorComparison d.b _ _ ≪≫ tensorIso
      (((P.ordinaryPullComposition d.b d.q₂).symm ≪≫
        leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) d.second).app L)
      (((P.ordinaryPullComposition d.b d.q₃).symm ≪≫
        leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) d.third).app M)) ≪≫
    (α_ _ _ _).symm

/-- Theta_L, with the canonical target and direct-image identifications inserted.
Source: the node's first iterated Omega formula
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryTripleLeft :
    ((P.ordinaryPush f₁).obj K ⊗ (P.ordinaryPush f₂).obj L) ⊗
        (P.ordinaryPush f₃).obj M ⟶
      (P.ordinaryPush (d.a ≫ (d.p₂ ≫ f₂))).obj (P.ordinaryTripleObject d K L M) :=
  (P.ordinaryProduct d.square₁₂ K L ⊗ₘ 𝟙 _) ≫
    P.ordinaryProduct d.squareL (P.ordinaryExternal d.p₁ d.p₂ K L) M ≫
    (P.ordinaryPush (d.c ≫ f₃)).map (P.ordinaryTripleLeftIdentification d K L M).hom ≫
    (P.ordinaryPushCongr d.squareL.w.symm).hom.app _

/-- Theta_R, with the source associator and the canonical common-target identifications.
Source: the node's second iterated Omega formula
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryTripleRight :
    ((P.ordinaryPush f₁).obj K ⊗ (P.ordinaryPush f₂).obj L) ⊗
        (P.ordinaryPush f₃).obj M ⟶
      (P.ordinaryPush (d.a ≫ (d.p₂ ≫ f₂))).obj (P.ordinaryTripleObject d K L M) :=
  (α_ _ _ _).hom ≫
    (𝟙 _ ⊗ₘ (P.ordinaryProduct d.square₂₃ L M ≫
      (P.ordinaryPushCongr d.square₂₃.w.symm).hom.app _)) ≫
    P.ordinaryProduct d.squareR K (P.ordinaryExternal d.q₂ d.q₃ L M) ≫
    (P.ordinaryPush (d.b ≫ (d.q₂ ≫ f₂))).map
      (P.ordinaryTripleRightIdentification d K L M).hom ≫
    (P.ordinaryPushCongr (d.squareR.w.symm.trans
      ((Category.assoc d.a d.p₁ f₁).trans
        (congrArg (fun z ↦ d.a ≫ z) d.square₁₂.w)))).hom.app _

/-- Pullback along the common structure map, factored through a specified projection.
Only equality transport and the canonical pullback compositor enter this isomorphism.
Source: the node's specified rho comparison
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryTripleFactor {T X : Scheme.{u}} (r : T ⟶ X) (f : X ⟶ B)
    (v : T ⟶ B) (h : v = r ≫ f) :
    P.ordinaryPull v ≅ P.ordinaryPull f ⋙ P.ordinaryPull r :=
  leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h ≪≫
    P.ordinaryPullComposition r f

/-- The specified triple transpose: split tensor, factor each pullback, then apply
exactly the three pulled-back adjunction counits, in order, without exchanging factors.
Source: the node's displayed three-counit arrow
(blueprint: def-pur-ordinary-product-transpose-data). -/
def ordinaryTripleCounit :
    (P.ordinaryPull (d.a ≫ (d.p₂ ≫ f₂))).obj
        (((P.ordinaryPush f₁).obj K ⊗ (P.ordinaryPush f₂).obj L) ⊗
          (P.ordinaryPush f₃).obj M) ⟶ P.ordinaryTripleObject d K L M :=
  let F₁ := (P.ordinaryPush f₁).obj K
  let F₂ := (P.ordinaryPush f₂).obj L
  let F₃ := (P.ordinaryPush f₃).obj M
  let v := d.a ≫ (d.p₂ ≫ f₂)
  let e₁ := (P.ordinaryTripleFactor (d.a ≫ d.p₁) f₁ v
    ((congrArg (fun z ↦ d.a ≫ z) d.square₁₂.w.symm).trans
      (Category.assoc d.a d.p₁ f₁).symm)).hom.app F₁
  let e₂ := (P.ordinaryTripleFactor (d.a ≫ d.p₂) f₂ v
    (Category.assoc d.a d.p₂ f₂).symm).hom.app F₂
  let e₃ := (P.ordinaryTripleFactor d.c f₃ v d.squareL.w).hom.app F₃
  (P.ordinaryTensorComparison v (F₁ ⊗ F₂) F₃).hom ≫
    ((P.ordinaryTensorComparison v F₁ F₂).hom ⊗ₘ 𝟙 _) ≫
    ((e₁ ⊗ₘ e₂) ⊗ₘ e₃) ≫
    (((P.ordinaryPull (d.a ≫ d.p₁)).map ((P.ordinaryAdj f₁).counit.app K) ⊗ₘ
      (P.ordinaryPull (d.a ≫ d.p₂)).map ((P.ordinaryAdj f₂).counit.app L)) ⊗ₘ
      (P.ordinaryPull d.c).map ((P.ordinaryAdj f₃).counit.app M))

/-- The binary pullback-tensor comparison followed by two specified maps.
This is a genuine composite, independent of any direct-image product map.
Source: blueprint relative Kunneth coherence proof, the two-counit formula
(blueprint: def-pur-ordinary-product-transpose-data). -/
@[irreducible] def ordinaryBinaryEvaluation {W X Y S : Scheme.{u}} {r : W ⟶ X} {t : W ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (sq : IsPullback r t f g)
    (F G : P.ordinaryCategory S) (K : P.ordinaryCategory X) (L : P.ordinaryCategory Y)
    (x : (P.ordinaryPull f).obj F ⟶ K) (y : (P.ordinaryPull g).obj G ⟶ L) :
    (P.ordinaryPull (t ≫ g)).obj (F ⊗ G) ⟶ P.ordinaryExternal r t K L :=
  (P.ordinaryTensorComparison (t ≫ g) F G).hom ≫
    ((P.ordinaryTripleFactor r f (t ≫ g) sq.w.symm).hom.app F ⊗ₘ
      (P.ordinaryPullComposition t g).hom.app G) ≫
    ((P.ordinaryPull r).map x ⊗ₘ (P.ordinaryPull t).map y)

/-- The common triple comparison followed by three arbitrary specified maps.
Specializing to pushforward objects and their counits is ordinaryTripleCounit.
Source: blueprint relative Kunneth coherence proof, ordered three-counit formula
(blueprint: def-pur-ordinary-product-transpose-data). -/
@[irreducible] def ordinaryTripleEvaluation
    (F₁ F₂ F₃ : P.ordinaryCategory B)
    (x : (P.ordinaryPull f₁).obj F₁ ⟶ K)
    (y : (P.ordinaryPull f₂).obj F₂ ⟶ L)
    (z : (P.ordinaryPull f₃).obj F₃ ⟶ M) :
    (P.ordinaryPull (d.a ≫ (d.p₂ ≫ f₂))).obj ((F₁ ⊗ F₂) ⊗ F₃) ⟶
      P.ordinaryTripleObject d K L M :=
  let v := d.a ≫ (d.p₂ ≫ f₂)
  let e₁ := (P.ordinaryTripleFactor (d.a ≫ d.p₁) f₁ v
    ((congrArg (fun z ↦ d.a ≫ z) d.square₁₂.w.symm).trans
      (Category.assoc d.a d.p₁ f₁).symm)).hom.app F₁
  let e₂ := (P.ordinaryTripleFactor (d.a ≫ d.p₂) f₂ v
    (Category.assoc d.a d.p₂ f₂).symm).hom.app F₂
  let e₃ := (P.ordinaryTripleFactor d.c f₃ v d.squareL.w).hom.app F₃
  (P.ordinaryTensorComparison v (F₁ ⊗ F₂) F₃).hom ≫
    ((P.ordinaryTensorComparison v F₁ F₂).hom ⊗ₘ 𝟙 _) ≫
    ((e₁ ⊗ₘ e₂) ⊗ₘ e₃) ≫
    (((P.ordinaryPull (d.a ≫ d.p₁)).map x ⊗ₘ
      (P.ordinaryPull (d.a ≫ d.p₂)).map y) ⊗ₘ (P.ordinaryPull d.c).map z)

end WeilConjectures.PurityFiniteSetting
