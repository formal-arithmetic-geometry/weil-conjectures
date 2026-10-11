/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A smooth separated connected curve is proper or affine

Source: Stacks Project, Varieties, Lemma 33.43.11 (Tag 0A28), and the blueprint
compactification route for `thm-sc-constant-invariance` (blueprint: lem-sc-proper-or-affine).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth separated connected curve over an algebraically closed field is proper or affine.
Source: Stacks Project, Varieties, Lemma 33.43.11 (Tag 0A28)
(blueprint: lem-sc-proper-or-affine).

Proof, step 1: by lem-sc-compactification, embed the curve as an open subscheme of a
proper smooth connected curve, with boundary a finite set of closed points. The algebraically
closed field hypothesis is part of def-sc-curves.
Step 2: if the boundary is empty, the open immersion is surjective and hence an isomorphism;
properness transfers from the compactification to the original curve. If the boundary is
nonempty, lem-sc-affine-open-proper says the open curve is affine. These cases exhaust all
possibilities. -/
theorem IsConnectedCurve.isProper_or_isAffine
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    IsProper f ∨ IsAffine C :=
  sorry

end AlgebraicGeometry
