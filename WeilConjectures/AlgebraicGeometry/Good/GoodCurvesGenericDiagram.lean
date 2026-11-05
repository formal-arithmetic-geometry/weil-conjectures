/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.Field.FieldCurveCompletionInsep
import WeilConjectures.AlgebraicGeometry.Field.FieldCurveNormalizationGoodOpen
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpreadMarkedCurveDiagram
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesFibreDensity

/-!
# Good curve diagrams near a generic point

Source: Stacks Project, More on Morphisms, Tag 0GK7, lemma-make-good-curves,
assertions (1)-(8) (blueprint: lem-weil-pbc-good-curves-generic-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
