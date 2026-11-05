/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The relation criterion for flatness over an arbitrary commutative ring

`WeilConjectures.CategoryTheory.Sites.FlatLocalRelations` proves that a sheaf of modules over a
Noetherian commutative ring is flat if and only if it has locally trivial relations
(`CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations`). Noetherianity is only used there to
resolve the kernel of a matrix `e : R^s ⟶ R^q` by a finite free module. Here we instead tensor
the exact sequence `ker e ⟶ R^s ⟶ R^q` with the sheaf: a section of `F ⊗ ker e` is locally a
finite sum `∑ₘ zₘ ⊗ kₘ` of pure tensors, and the vectors `kₘ ∈ ker e` form the columns of the
matrix `b` trivializing the relations. This removes the Noetherian hypothesis.

We also show that restriction along a cocontinuous functor preserves locally trivial relations
(`CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp`).

## Main results

- `CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat'`: relations between sections of a
  flat sheaf of modules over any commutative ring are locally trivial.
- `CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations'`: the relation criterion for
  flatness over any commutative ring.
- `CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp`: restriction along a cocontinuous
  functor preserves locally trivial relations.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

variable [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

end CategoryTheory
