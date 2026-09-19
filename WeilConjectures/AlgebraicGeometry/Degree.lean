/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# The degree of a finite morphism

The *degree* of a finite morphism `f : X ⟶ Y` onto an irreducible scheme is the generic rank of
the direct image `f_* 𝒪_X` of the structure sheaf, that is the dimension of `(f_* 𝒪_X)_{η_Y}`
over the function field `κ(η_Y)` of `Y`.

Finiteness is what makes this the degree: it is what makes `f_* 𝒪_X` coherent, so that the
stalk at the generic point is a finite-dimensional vector space. For a morphism which is not
finite the generic rank of `f_* 𝒪_X` need not be finite, and `Module.finrank` would return the
junk value `0`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.degree`: the degree `deg f` of a finite morphism onto an
  irreducible scheme (blueprint: `def:deg-finite-morphism`).

## TODO

Two statements about the degree are not formalised here:

* that `deg f = [κ(η_X) : κ(η_Y)]` for `f` finite surjective between integral schemes. This
  needs the identification of the stalk of `f_* 𝒪_X` at `η_Y` with the ring of the generic
  fibre of `f`, that is with the function field of `X`.
* that for flat `f` the degree agrees with the rank of the locally free sheaf `f_* 𝒪_X`, the
  degree of `def:av-degree`. This needs the constancy of the rank of a locally free sheaf on a
  connected scheme.

## References

* The blueprint chapter on the degree of an isogeny, section `sec:deg-intersection`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IrreducibleSpace Y]

/-- **The degree of a finite morphism** onto an irreducible scheme: the generic rank of the
direct image `f_* 𝒪_X` of the structure sheaf. -/
noncomputable def degree : ℕ :=
  Modules.genericRank ((Modules.pushforward f).obj X.structureModules)

end AlgebraicGeometry.Scheme.Hom
