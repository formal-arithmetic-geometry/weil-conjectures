/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!

# The tensor product of étale and pro-étale sheaves preserves colimits

The K-flat left derivability structure requires the tensor product of the sheaf category
to interact well with the coproducts defining the tensor product of complexes and with
`ℤ`-indexed colimits. All of these conditions — `GradedObject.HasTensor₄ObjExt`,
`GradedObject.HasGoodTensor₁₂Tensor`, `GradedObject.HasGoodTensorTensor₂₃` and the
preservation of `ℤ`-indexed colimits in each variable — unfold to the statement that
`tensorLeft X` or `tensorRight X` preserves a colimit of size `0`. This file proves the
single instance they all follow from, for the monoidal structures of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.

The proof is Day's reflection theorem
(`CategoryTheory.Monoidal.Reflective.monoidalClosed`), which makes the sheaf category
monoidal closed and hence `tensorLeft X` a left adjoint. Its inputs are all available for
the small étale site of `Y` — and, verbatim, for the pro-étale site `Y.ProEt`, since the
argument uses nothing about the site beyond the sheafification adjunction:

* the presheaf category `Y.Etaleᵒᵖ ⥤ A` is monoidal closed for the objectwise monoidal
  structure, by `CategoryTheory.MonoidalClosed.FunctorCategory.monoidalClosed`, whose
  internal hom is the enriched functor hom. This is a *scoped* instance, hence the
  `open scoped` below. Its enriched-hom side conditions are limits of size `u + 1`,
  supplied by `CategoryTheory.IsGrothendieckAbelian.hasLimits` exactly as for the
  monoidality of `W` in the sibling file `Defs`;
* the presheaf category is *symmetric* monoidal, which is what Day's theorem asks of the
  ambient category and is the only reason `A` is assumed symmetric rather than merely
  braided here — this is the sole extra hypothesis this file adds to those of `Defs`;
* `presheafToSheaf` is monoidal and `sheafToPresheaf` is fully faithful, both instances
  of `CategoryTheory.Sheaf.monoidalCategory`'s file for the monoidal structures of `Defs`.

Note that the resulting `Etale.sheafMonoidalClosed` is over the monoidal structure of
`Defs` (the sheafification of the objectwise tensor product), *not* over a cartesian one:
mathlib's `instMonoidalClosedSheafOfHasSheafifyOfFunctorOpposite` produces a monoidal
closed structure for the cartesian tensor on a full monoidal subcategory of presheaves,
which is a different instance and moreover unavailable here, since the coefficient
categories of this development are abelian and a non-trivial additive category is never
cartesian closed.

## Main results

- `AlgebraicGeometry.Etale.sheafMonoidalClosed` and
  `AlgebraicGeometry.ProEtale.sheafMonoidalClosed`: the categories of `A`-valued étale and
  pro-étale sheaves are monoidal closed.
- `AlgebraicGeometry.Etale.preservesColimitsOfSize_tensorLeft_sheaf` and
  `AlgebraicGeometry.ProEtale.preservesColimitsOfSize_tensorLeft_sheaf`: tensoring on the
  left with a fixed étale, respectively pro-étale, sheaf preserves colimits of size `0`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped MonoidalClosed.FunctorCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

/- The monoidal structure on the coefficient category, as in the sibling file `Defs`,
except that the braiding is strengthened to a symmetry: Day's reflection theorem is
stated for a symmetric ambient category. This still holds, and is a mathlib instance, in
the intended application `A = ModuleCat.{u + 1} Λ` with `Λ` a commutative ring. -/
variable [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]

/-- The category of `A`-valued étale sheaves is monoidal closed, for the monoidal
structure `Etale.sheafMonoidalCategory` of the sibling file `Defs`.

This is Day's reflection theorem applied to the sheafification adjunction
`presheafToSheaf ⊣ sheafToPresheaf`: the left adjoint is monoidal, the right adjoint is
fully faithful, and the presheaf category is symmetric monoidal closed. -/
noncomputable instance Etale.sheafMonoidalClosed :
    MonoidalClosed (Sheaf Y.smallEtaleTopology A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction Y.smallEtaleTopology A)

/-- Tensoring on the left with a fixed `A`-valued étale sheaf preserves colimits of size
`0`, since it is left adjoint to the internal hom of `Etale.sheafMonoidalClosed`.
Together with the braiding this gives every compatibility between the tensor product of
étale sheaves and colimits that the K-flat left derivability structure asks for. -/
instance Etale.preservesColimitsOfSize_tensorLeft_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

/-- Tensoring on the right with a fixed `A`-valued étale sheaf preserves colimits of size
`0`, by `Etale.preservesColimitsOfSize_tensorLeft_sheaf` and the braiding. -/
instance Etale.preservesColimitsOfSize_tensorRight_sheaf (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) where
  preservesColimitsOfShape := ⟨inferInstance⟩

/-- The category of `A`-valued pro-étale sheaves is monoidal closed, for the monoidal
structure `ProEtale.sheafMonoidalCategory` of the sibling file `Defs`.

This is `Etale.sheafMonoidalClosed` for the pro-étale site: Day's reflection theorem uses
nothing about the site beyond the sheafification adjunction, so the argument applies
verbatim. -/
noncomputable instance ProEtale.sheafMonoidalClosed :
    MonoidalClosed (Sheaf (Scheme.ProEt.topology Y) A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction (Scheme.ProEt.topology Y) A)

/-- Tensoring on the left with a fixed `A`-valued pro-étale sheaf preserves colimits of
size `0`, exactly as in the étale case: it is left adjoint to the internal hom of
`ProEtale.sheafMonoidalClosed`. -/
instance ProEtale.preservesColimitsOfSize_tensorLeft_sheaf
    (X : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

/-- Tensoring on the right with a fixed `A`-valued pro-étale sheaf preserves colimits of
size `0`, by `ProEtale.preservesColimitsOfSize_tensorLeft_sheaf` and the braiding. -/
instance ProEtale.preservesColimitsOfSize_tensorRight_sheaf
    (X : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) where
  preservesColimitsOfShape := ⟨inferInstance⟩

end AlgebraicGeometry
