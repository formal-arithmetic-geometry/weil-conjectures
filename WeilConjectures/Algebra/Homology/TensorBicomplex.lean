/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Tensoring a chain map with a module map

Source: Stacks Project, Algebra, Tag 00M3, first paragraph of the proof.
(blueprint: def-weil-pbc-tensor-bicomplex)

The unsigned tensor bicomplex of two chain complexes `P` and `Q` of the node, with terms
`Pᵢ ⊗ Qⱼ`, is Mathlib's
`((Functor.mapBifunctorHomologicalComplex (curriedTensor _) _ _).obj P).obj Q`, and its action on
pairs of chain maps is the `map` of that functor.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace ChainComplex

variable {R : Type u} [CommRing R]

end ChainComplex
