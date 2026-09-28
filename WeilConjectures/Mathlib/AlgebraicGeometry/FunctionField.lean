/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# The generic point as a morphism from the spectrum of the function field

For an integral scheme `X`, `Scheme.functionField` is the stalk of the structure sheaf at the
generic point, and `Scheme.fromSpecStalk` turns a stalk into a morphism from its spectrum.
This file names the composite, the canonical morphism `Spec k(X) ⟶ X`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism `Spec k(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme `X`, namely `Scheme.fromSpecStalk` at the generic point. -/
noncomputable abbrev fromSpecFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

end AlgebraicGeometry.Scheme
