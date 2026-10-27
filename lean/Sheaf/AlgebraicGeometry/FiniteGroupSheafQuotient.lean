/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Constant-group sheaf torsors and their quotient atlas

Source: Stacks Project, examples-stacks.tex, Tags 0371 and 04WM
(blueprint: def-sfb-constant-group-sheaf-quotient).

Actions and equivariant morphisms are Mathlib `Action`. The quotient is the core
of the full subcategory of equivariant maps whose source is locally regular.
Its atlas fibre can be computed in the ambient core: a full inclusion does not
change the isomorphisms between its objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ConstantGroupSheafQuotient

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (H : Type w) [Group H] [HasSheafify J (Type w)]

/-- The constant group sheaf with its left regular action, constructed by sheafification.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def regular : Action (Sheaf J (Type w)) H :=
  ((constantSheaf J (Type w)).mapAction H).obj (Action.ofMulAction H H)

/-- The constant section labelled by a group element, including on disconnected objects.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def label (U : C) (h : H) : (regular J H).V.obj.obj (op U) :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj H)).app (op U) h

/-- Local triviality is an equivariant identification with the regular sheaf after
restriction to every arrow of a covering sieve. This imposes no global section.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def IsLocallyRegular (P : Action (Sheaf J (Type w)) H) : Prop :=
  ∀ U : C, ∃ R : Sieve U, R ∈ J U ∧
    ∀ (V : C) (a : V ⟶ U), R a →
      Nonempty
        (((J.overPullback (Type w) V).mapAction H).obj (regular J H) ≅
          ((J.overPullback (Type w) V).mapAction H).obj P)

variable {H}

/-- The quotient groupoid of locally trivial sheaf torsors with equivariant map to `A`.
An arrow is an equivariant sheaf isomorphism commuting with that map.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
abbrev quotient (A : Action (Sheaf J (Type w)) H) :=
  Core (ObjectProperty.FullSubcategory (fun X : Over A ↦ IsLocallyRegular J H X.left))

/-- Forget the local-triviality proof and retain the actual equivariant map.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def quotientForget (A : Action (Sheaf J (Type w)) H) : quotient J A ⥤ Over A :=
  Core.inclusion _ ⋙ ObjectProperty.ι _

variable {t : C} (ht : IsTerminal t) (A : Action (Sheaf J (Type w)) H)

/-- Extend `h ↦ h • z` by the constant-sheaf adjunction.
Source: Stacks 04WM (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def orbitMap (z : A.V.obj.obj (op t)) : (regular J H).V ⟶ A.V :=
  ((constantSheafAdj J (Type w) ht).homEquiv H A.V).symm
    (TypeCat.ofHom (fun h : H ↦ (A.ρ h).hom.app (op t) z))

/-- The constructed orbit map is equivariant.
Source: Stacks 04WM (blueprint: def-sfb-constant-group-sheaf-quotient).
Proof: precompose with the unit from the constant presheaf. Both composites send
`h` to `(g*h) • z = g • (h • z)`. Injectivity of the sheafification adjunction
on morphisms proves the equation. -/
theorem orbitMap_equivariant (z : A.V.obj.obj (op t)) (g : H) :
    (regular J H).ρ g ≫ orbitMap J ht A z = orbitMap J ht A z ≫ A.ρ g := by
  sorry

/-- The trivial torsor with its specified equivariant orbit map.
Source: Stacks 04WM (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def trivial (z : A.V.obj.obj (op t)) : Over A :=
  Over.mk (Action.Hom.mk (orbitMap J ht A z) (orbitMap_equivariant J ht A z))

/-- The canonical atlas maps a section to its trivial torsor.
Source: Stacks 04WM (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def atlas : Discrete (A.V.obj.obj (op t)) ⥤ Core (Over A) :=
  Discrete.functor (fun z ↦ Core.mk (trivial J ht A z))

/-- The actual iso-comma 2-fibre product with a point `xi`: objects are `(z,eta)`.
Source: Stacks 04M9 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
abbrev atlasFiber (xi : Over A) :=
  GroupoidTwoFiberProduct (atlas J ht A)
    ((Functor.const (Discrete PUnit)).obj (Core.mk xi))

/-- The sheaf isomorphism specified by an object of the 2-fibre product.
Source: Stacks 04WM (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def comparison {xi : Over A} (L : atlasFiber J ht A xi) :
    (regular J H).V ≅ xi.left.V :=
  (Action.forget _ H).mapIso ((Over.forget A).mapIso L.of.hom.iso)

/-- Evaluation of the specified equivariant isomorphism at the identity section.
Source: Stacks 0371 and 04WM (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def evaluation {xi : Over A} (L : atlasFiber J ht A xi) :
    xi.left.V.obj.obj (op t) :=
  (comparison J ht A L).hom.hom.app (op t) (label J H t 1)

/-- Restrict the equivariant map by the slice forgetful functor.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def restrict (xi : Over A) (U : C) :
    Over (((J.overPullback (Type w) U).mapAction H).obj A) :=
  (Over.post ((J.overPullback (Type w) U).mapAction H)).obj xi

/-- Restrict the action to a slice, retaining its actual action maps.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def onSlice (U : C) : Action (Sheaf (J.over U) (Type w)) H :=
  ((J.overPullback (Type w) U).mapAction H).obj A

/-- The atlas fibre over any test object, using the restricted torsor.
Source: Stacks 04M9 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
abbrev fiberAt (xi : Over A) (U : C) [HasSheafify (J.over U) (Type w)] :=
  atlasFiber (J.over U) Over.mkIdTerminal (onSlice J A U) (restrict J A xi U)

/-- Evaluation at the identity in the atlas fibre over a variable test object.
Source: Stacks 0371 (blueprint: def-sfb-constant-group-sheaf-quotient). -/
def evaluateAt (xi : Over A) (U : C) [HasSheafify (J.over U) (Type w)]
    (L : fiberAt J A xi U) : xi.left.V.obj.obj (op U) :=
  evaluation (J.over U) Over.mkIdTerminal (onSlice J A U) L

end AlgebraicGeometry.ConstantGroupSheafQuotient
