/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.SheafCompose

/-!

# Sheaf-preserving postcomposition on the small étale sites

Postcomposition with a limit-preserving functor preserves sheaves on the small étale
site of a scheme. This does not follow from `hasSheafCompose_of_preservesLimitsOfSize`
directly, since the covering sieves of the small étale site are indexed by a large
type; it is instead transported from the small affine étale site, which is
`1`-hypercover dense and essentially small. The instance for the forgetful functor of
the concrete coefficient category is what allows checking statements about `A`-valued
étale sheaves on their stalks; it is the input to the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.

-/

@[expose] public section

universe v'' u'' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Postcomposition with a limit-preserving functor preserves sheaves on the small
étale site. This does not follow from `hasSheafCompose_of_preservesLimitsOfSize`
directly, since the covering sieves of the small étale site are indexed by a large
type; it is instead transported from the small affine étale site, which is
`1`-hypercover dense and essentially small. -/
lemma Etale.hasSheafCompose_smallEtaleTopology {B : Type u''} [Category.{v''} B]
    (F : A ⥤ B) [PreservesLimitsOfSize.{u, u} F] :
    Y.smallEtaleTopology.HasSheafCompose F :=
  GrothendieckTopology.hasSheafCompose_of_isOneHypercoverDense
    (Scheme.AffineEtale.Spec Y) (Scheme.AffineEtale.topology Y) _ F

/-- Postcomposition with the forgetful functor of the concrete coefficient category
preserves étale sheaves. This is the instance of
`Etale.hasSheafCompose_smallEtaleTopology` needed to check statements about étale
sheaves on their stalks; it is restricted to `forget A` so that instance search never
considers it for goals mentioning an unknown functor. -/
instance Etale.hasSheafCompose_forget_smallEtaleTopology :
    Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A) :=
  Etale.hasSheafCompose_smallEtaleTopology A Y _

end AlgebraicGeometry
