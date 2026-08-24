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
`1`-hypercover dense and essentially small.

This was used to check statements about `A`-valued étale sheaves on their stalks, for
the stalkwise proof that the class of sheafification-inverting morphisms of presheaves
is monoidal. That proof has been replaced by the closed-braided argument of
`CategoryTheory.GrothendieckTopology.W.monoidal`, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`, so no concreteness
hypothesis on the coefficient category is needed here any more.

-/

@[expose] public section

universe v'' u'' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A]

variable (Y : Scheme.{u})

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

end AlgebraicGeometry
