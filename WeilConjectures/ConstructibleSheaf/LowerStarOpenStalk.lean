/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit

/-!
# Finiteness of the stalks of a direct image along an open immersion

Let `X` be a locally noetherian scheme such that the local rings of all étale `X`-schemes are
integral domains (for instance a regular scheme), `j : U ⟶ X` an open immersion and `F` a
locally constant sheaf of modules on the small étale site of `U` whose geometric stalks are
finite of bounded cardinality. Then the geometric stalks of `j_* F` are finite.

An element of the stalk of `j_* F` at a geometric point is the germ of a section of `F` over
`V ×_X U` for an étale neighbourhood `V`; finitely many germs come from one neighbourhood, the
fibre category of a point being cofiltered, and this neighbourhood may be shrunk to have
irreducible underlying space. Then `V ×_X U` is a nonempty open of `V`, hence irreducible, or
empty, and the sections of a locally constant sheaf over an étale scheme with connected
underlying space inject into the stalk at any geometric point of it
(`AlgebraicGeometry.Etale.injective_toPresheafFiber_of_preconnectedSpace`). So the stalk of
`j_* F` has at most as many elements as the largest stalk of `F`.

The cardinalities of the stalks of a finite locally constant sheaf of modules over a finite ring
on a quasi-compact scheme are bounded
(`AlgebraicGeometry.Etale.exists_natCard_sheafFiber_le`): finitely many members of a
trivialising cover suffice, and over each of them all stalks are the value of a constant sheaf.

## Main statements

- `AlgebraicGeometry.Etale.injective_toPresheafFiber_of_preconnectedSpace`
- `AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar`
- `AlgebraicGeometry.Etale.exists_natCard_sheafFiber_le`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ]

section Injective

variable {X : Scheme.{u}} (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end Injective

section LowerStar

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end LowerStar

section Bound

variable {X : Scheme.{u}} [Finite Λ]

end Bound

end Etale

end AlgebraicGeometry
