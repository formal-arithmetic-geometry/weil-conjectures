/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Algebraic moduli stacks and smoothness

Source: Stacks Project, Algebraic Stacks, definition-algebraic-stack; Morphisms of Stacks,
definition of smooth morphisms (blueprint: def-sfb-algebraic-moduli-stack).

The fibred-groupoid, descent, and algebraic-space 2-base-change notions are the existing
ones. Atlas properties refer to the actual projection in each such base change.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Smoothness on every étale scheme chart of an algebraic-space map to a scheme.
Source: Stacks Project, Morphisms of Spaces, smooth morphisms
(blueprint: def-sfb-algebraic-moduli-stack). -/
def SpaceMapIsSmooth {S : AlgebraicGeometry.Scheme.{u}}
    (Z : AlgebraicGeometry.AlgebraicSpace S) (T : Over S) (a : Z.obj.obj ⟶ yoneda.obj T) :
    Prop :=
  ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj), AlgebraicGeometry.AlgebraicSpace.IsEtale b →
    AlgebraicGeometry.Smooth ((yoneda.preimage (b ≫ a)).left)

/-- A smooth surjective scheme atlas, representable by algebraic spaces.
Source: Stacks Project, Algebraic Stacks, definition-algebraic-stack
(blueprint: def-sfb-algebraic-moduli-stack). -/
def IsSmoothModuliAtlas {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (U : Over S)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSmooth Z T p ∧ SpaceMapIsSurjective Z T p

/-- An étale stack with algebraic-space diagonal and a smooth surjective scheme atlas.
Source: Stacks Project, Algebraic Stacks, definition-algebraic-stack
(blueprint: def-sfb-algebraic-moduli-stack). -/
def IsAlgebraicModuliStack {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  IsModuliStack F ∧ HasAlgebraicSpaceDiagonal F ∧
    ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a

/-- Smoothness over the base: a smooth scheme atlas has smooth structural composite.
Source: Stacks Project, Morphisms of Stacks, smooth morphisms
(blueprint: def-sfb-algebraic-moduli-stack). -/
def IsSmoothModuliStack {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    IsSmoothModuliAtlas F U a ∧ AlgebraicGeometry.Smooth U.hom

end CategoryTheory
