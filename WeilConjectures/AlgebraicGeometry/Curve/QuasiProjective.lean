/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProduct
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Integral curves are quasi-projective

WIP
-/

@[expose] public section

open Polynomial IsLocalRing

namespace AlgebraicGeometry

universe u

open CategoryTheory Limits TopologicalSpace

variable {X : Scheme.{u}}

end AlgebraicGeometry

namespace AlgebraicGeometry

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

variable {X : Scheme.{u}}

end AlgebraicGeometry
