/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.Sites.InverseImageDifferentials
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Square-zero extensions of sheaves of commutative algebras

Source: Stacks Project, Deformation Theory, Tags 0GPZ, 0GQ0, 0GQ2 and 08U8
(blueprint: def-sfb-square-zero-sheaf-algebra).

Extensions retain the actual sheaf of rings, its base and quotient maps, and the
specified additive kernel identification. Morphisms may change the coefficient
module. The Baer diagram is expressed on local pairs with equal quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SquareZeroSheaf

/-- Module sheaves over the given commutative ring sheaf. Source: Stacks 0GPZ
(blueprint: def-sfb-square-zero-sheaf-algebra). -/
abbrev Modules {T : TopCat.{u}} (A : T.Sheaf CommRingCat.{u}) :=
  ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring A)

/-- An exact square-zero extension with its specified quotient action on the kernel.
Exactness at the middle is sectionwise; the quotient is only locally surjective.
Source: Stacks 0GPZ (blueprint: def-sfb-square-zero-sheaf-algebra). -/
structure Extension {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    (f : R ⟶ A) (G : Modules A) where
  ring : T.Sheaf CommRingCat.{u}
  base : R ⟶ ring
  p : ring ⟶ A
  base_p : base ≫ p = f
  i : ∀ V : (Opens T)ᵒᵖ, G.val.obj V →+ ring.obj.obj V
  i_natural : ∀ {V W : (Opens T)ᵒᵖ} (r : V ⟶ W) (g : G.val.obj V),
    i W (G.val.map r g) = ring.obj.map r (i V g)
  injective : ∀ V : (Opens T)ᵒᵖ, Function.Injective (i V)
  kernel : ∀ (V : (Opens T)ᵒᵖ) (e : ring.obj.obj V),
    p.hom.app V e = 0 ↔ ∃ g : G.val.obj V, i V g = e
  surjective : CategoryTheory.Presheaf.IsLocallySurjective
    (Opens.grothendieckTopology T) p.hom
  square_zero : ∀ (V : (Opens T)ᵒᵖ) (g h : G.val.obj V), i V g * i V h = 0
  action : ∀ (V : (Opens T)ᵒᵖ) (e : ring.obj.obj V) (g : G.val.obj V),
    e * i V g = i V ((p.hom.app V e) • g)

/-- A coefficient-changing morphism of extensions; on the base and quotient it is
identity. Source: Stacks 0GQ2 (blueprint: def-sfb-square-zero-sheaf-algebra). -/
structure Hom {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G H : Modules A} (E : Extension f G) (F : Extension f H) (v : G ⟶ H) where
  map : E.ring ⟶ F.ring
  base : E.base ≫ map = F.base
  quotient : map ≫ F.p = E.p
  kernel : ∀ (V : (Opens T)ᵒᵖ) (g : G.val.obj V),
    map.hom.app V (E.i V g) = F.i V (v.val.app V g)

/-- An isomorphism of extensions fixes both named ends, including the kernel
identification. Source: Stacks 0GPZ (blueprint: def-sfb-square-zero-sheaf-algebra). -/
structure Iso {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E F : Extension f G) where
  ringIso : E.ring ≅ F.ring
  base : E.base ≫ ringIso.hom = F.base
  quotient : ringIso.hom ≫ F.p = E.p
  kernel : ∀ (V : (Opens T)ᵒᵖ) (g : G.val.obj V),
    ringIso.hom.hom.app V (E.i V g) = F.i V g

/-- A split extension, specified by its algebra section. The isomorphism from
`A ⊕ G` is `(a,g) ↦ s(a) + i(g)`; the extension axioms give multiplication
`(a,g)(b,h) = (ab, a • h + b • g)`.
Source: Stacks 0GPZ (blueprint: def-sfb-square-zero-sheaf-algebra). -/
def IsSplit {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E : Extension f G) : Prop :=
  ∃ s : A ⟶ E.ring, s ≫ E.p = 𝟙 A ∧ f ≫ s = E.base

/-- The fibre-product-then-addition description of a Baer sum. The local map `b`
is a ring map on pairs with equal quotient, over `R` and `A`, whose kernel map
is addition. Thus its target is the coefficient pushout of `E₁ ×_A E₂`.
Source: Stacks 0GQ0 and 0GQ2 (blueprint: def-sfb-square-zero-sheaf-algebra). -/
structure Baer {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}} {f : R ⟶ A}
    {G : Modules A} (E₁ E₂ E₃ : Extension f G) where
  b : ∀ V : (Opens T)ᵒᵖ, ∀ x : E₁.ring.obj.obj V, ∀ y : E₂.ring.obj.obj V,
    E₁.p.hom.app V x = E₂.p.hom.app V y → E₃.ring.obj.obj V
  naturality : ∀ {V W : (Opens T)ᵒᵖ} (r : V ⟶ W)
    (x : E₁.ring.obj.obj V) (y : E₂.ring.obj.obj V)
    (h : E₁.p.hom.app V x = E₂.p.hom.app V y)
    (h' : E₁.p.hom.app W (E₁.ring.obj.map r x) =
      E₂.p.hom.app W (E₂.ring.obj.map r y)),
    b W _ _ h' = E₃.ring.obj.map r (b V x y h)
  add : ∀ (V : (Opens T)ᵒᵖ) (x x' : E₁.ring.obj.obj V)
    (y y' : E₂.ring.obj.obj V)
    (h : E₁.p.hom.app V x = E₂.p.hom.app V y)
    (h' : E₁.p.hom.app V x' = E₂.p.hom.app V y')
    (hs : E₁.p.hom.app V (x + x') = E₂.p.hom.app V (y + y')),
    b V (x + x') (y + y') hs = b V x y h + b V x' y' h'
  mul : ∀ (V : (Opens T)ᵒᵖ) (x x' : E₁.ring.obj.obj V)
    (y y' : E₂.ring.obj.obj V)
    (h : E₁.p.hom.app V x = E₂.p.hom.app V y)
    (h' : E₁.p.hom.app V x' = E₂.p.hom.app V y')
    (hm : E₁.p.hom.app V (x * x') = E₂.p.hom.app V (y * y')),
    b V (x * x') (y * y') hm = b V x y h * b V x' y' h'
  one : ∀ (V : (Opens T)ᵒᵖ) (h : E₁.p.hom.app V 1 = E₂.p.hom.app V 1),
    b V 1 1 h = 1
  base : ∀ (V : (Opens T)ᵒᵖ) (a : R.obj.obj V)
    (h : E₁.p.hom.app V (E₁.base.hom.app V a) =
      E₂.p.hom.app V (E₂.base.hom.app V a)),
    b V _ _ h = E₃.base.hom.app V a
  quotient : ∀ (V : (Opens T)ᵒᵖ) (x : E₁.ring.obj.obj V) (y : E₂.ring.obj.obj V)
    (h : E₁.p.hom.app V x = E₂.p.hom.app V y),
    E₃.p.hom.app V (b V x y h) = E₁.p.hom.app V x
  kernel : ∀ (V : (Opens T)ᵒᵖ) (g h : G.val.obj V)
    (hk : E₁.p.hom.app V (E₁.i V g) = E₂.p.hom.app V (E₂.i V h)),
    b V _ _ hk = E₃.i V (g + h)

/-- Restriction of modules is the actual continuous pushforward from the opens
of the subspace to their ambient images. Source: Stacks 0GQ2
(blueprint: def-sfb-square-zero-sheaf-algebra). -/
def openModules {T : TopCat.{u}} (A : T.Sheaf CommRingCat.{u}) (U : Opens T) :
    Modules A ⥤ Modules (T := TopCat.of U) ((U.sheafRestrict (C := CommRingCat.{u})).obj A) :=
  SheafOfModules.overFunctor (CategoryTheory.SheafDifferentials.ring A) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((CategoryTheory.SheafDifferentials.ring A).over U))
      (D := SheafOfModules.{u} (U.sheafRestrict.obj (CategoryTheory.SheafDifferentials.ring A)))
      (U.sheafOfModulesEquivOver (CategoryTheory.SheafDifferentials.ring A))

/-- A restricted extension, characterized by the actual open restriction of its
ring and its named kernel map. This relation avoids choosing proof fields.
Source: Stacks 0GQ2 (blueprint: def-sfb-square-zero-sheaf-algebra). -/
structure OpenRestriction {T : TopCat.{u}} {R A : T.Sheaf CommRingCat.{u}}
    {f : R ⟶ A} {G : Modules A} (E : Extension f G) (U : Opens T)
    (F : Extension (T := TopCat.of U) ((U.sheafRestrict (C := CommRingCat.{u})).map f)
      ((openModules A U).obj G)) where
  ringIso : (U.sheafRestrict (C := CommRingCat.{u})).obj E.ring ≅ F.ring
  base : (U.sheafRestrict (C := CommRingCat.{u})).map E.base ≫ ringIso.hom = F.base
  quotient : ringIso.hom ≫ F.p = (U.sheafRestrict (C := CommRingCat.{u})).map E.p
  kernel : ∀ (V : (Opens (TopCat.of U))ᵒᵖ)
    (g : G.val.obj (U.isOpenEmbedding.isOpenMap.functor.op.obj V)),
    ringIso.hom.hom.app V (E.i (U.isOpenEmbedding.isOpenMap.functor.op.obj V) g) = F.i V g

end TopCat.SquareZeroSheaf
