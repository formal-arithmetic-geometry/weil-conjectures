/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterionAux

/-!
# The induction step of Deligne's finiteness criterion at closed points

If the cohomology sheaves of a bounded below complex `G` on a proper scheme over a separably
closed field are constructible below degree `q`, if `RΓ(X, G)` has finite cohomology and if
`ℋ^q(G)` has a constructible subsheaf with quotient supported at closed points, then `ℋ^q(G)` is
constructible (`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_of_forall_lt`). This is the
inductive step of `WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory.TStructure (t)

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

end Etale

end AlgebraicGeometry
