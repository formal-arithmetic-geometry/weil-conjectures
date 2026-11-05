/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.ConstructibleApproximation
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FiniteSections
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Hypercohomology
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Acyclic
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Detection
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso

/-!
# Auxiliary lemmas for Deligne's finiteness criterion at closed points

Finiteness of the cohomology of bounded constructible complexes on separably closed points and on
proper schemes over a separably closed field, stalks of pullbacks at the points of a source, and
the bounded constructibility of truncations, used in
`WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory.TStructure (t)

section Auxiliary

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable {k : Type u} [Field k] [IsSepClosed k]

end Auxiliary

end Etale

end AlgebraicGeometry
