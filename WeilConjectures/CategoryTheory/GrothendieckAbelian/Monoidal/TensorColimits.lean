/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!

# The tensor product of étale sheaves preserves colimits (sorried)

The K-flat left derivability structure requires the tensor product of the sheaf category
to interact well with the coproducts defining the tensor product of complexes and with
`ℤ`-indexed colimits. All of these conditions — `GradedObject.HasTensor₄ObjExt`,
`GradedObject.HasGoodTensor₁₂Tensor`, `GradedObject.HasGoodTensorTensor₂₃` and the
preservation of `ℤ`-indexed colimits in each variable — unfold to the statement that
`tensorLeft X` or `tensorRight X` preserves a colimit of size `0`. This file records the
single instance they all follow from, for the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.

The intended proof, which is not yet formalized, is the following. Write
`L = presheafToSheaf` and `ι = sheafToPresheaf`. A colimit of sheaves is the
sheafification of the colimit of the underlying presheaves, `L` is a monoidal functor and
`X ≅ L (ι X)`, so for a diagram `F` of étale sheaves
`X ⊗ colim F ≅ L (ι X ⊗ colim (F ⋙ ι)) ≅ L (colim (F ⋙ ι ⋙ tensorLeft (ι X)))
  ≅ colim (F ⋙ tensorLeft X)`,
the middle isomorphism because the tensor product of presheaves is computed objectwise
and `a ⊗ -` preserves colimits in `A`, `A` being monoidal closed
(`CategoryTheory.MonoidalClosed.instPreservesColimitsTensorLeft`).

Alternatively, Day's reflection theorem (`CategoryTheory.Monoidal.Reflective.monoidalClosed`)
would make `Sheaf Y.smallEtaleTopology A` monoidal closed, making `tensorLeft X` a left
adjoint. That route needs a `MonoidalClosed` instance on the *presheaf* category for the
objectwise monoidal structure, which mathlib does not yet provide.

## Sorried instances

- `AlgebraicGeometry.Etale.preservesColimitsOfSize_tensorLeft_sheaf`: tensoring on the
  left with a fixed étale sheaf preserves colimits of size `0`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- Tensoring on the left with a fixed `A`-valued étale sheaf preserves colimits of size
`0`; see the module docstring for the intended proof. Together with the braiding this
gives every compatibility between the tensor product of étale sheaves and colimits that
the K-flat left derivability structure asks for. -/
instance Etale.preservesColimitsOfSize_tensorLeft_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  sorry

/-- Tensoring on the right with a fixed `A`-valued étale sheaf preserves colimits of size
`0`, by `Etale.preservesColimitsOfSize_tensorLeft_sheaf` and the braiding. -/
instance Etale.preservesColimitsOfSize_tensorRight_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) where
  preservesColimitsOfShape := ⟨inferInstance⟩

end AlgebraicGeometry
