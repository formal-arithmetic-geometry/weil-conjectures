/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Finite.Exact

/-! # Brauer pullback along finite modifications of reduced curves

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 2.
(blueprint: lem-sc-brauer-finite-modification-injection)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- A finite morphism which is an isomorphism over a dense open of a reduced curve
induces an injection on its cohomological Brauer group.
Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/
lem-sc-brauer-zero-all-curves.md, Proof, Step 2 (normalization).
(blueprint: lem-sc-brauer-finite-modification-injection)

Proof: finiteness makes the image closed, and the isomorphism over the dense open V
makes it dense, so ν is surjective. The map G_m,C → ν_* G_m,Y is a monomorphism:
a unit whose pullback is 1 differs from 1 by a function vanishing in all residue fields,
by surjectivity; an etale scheme over reduced C is reduced, so that function is zero.
Let Q be the cokernel. Restriction to V is zero because ν is an isomorphism there.
The complement Z = C ∖ V is a finite set of closed points: it contains no generic point,
and C is Noetherian of dimension at most one. Give Z its reduced subscheme structure.
The geometric-stalk criterion identifies Q with i_* i^* Q for i : Z → C. The residue
fields of these closed points are k, since C is finite type over algebraically closed k.
Thus Z is a finite disjoint union of Spec k. Cohomology on a separably closed point
vanishes in positive degree for every abelian coefficient sheaf, so H^1(C,Q) = 0,
using exact finite pushforward for i. The long exact sequence for
0 → G_m,C → ν_* G_m,Y → Q → 0 injects H^2(C,G_m) into H^2(C,ν_* G_m,Y).
Exact finite pushforward for ν identifies the target with H^2(Y,G_m); under this
identification the map is precisely canonical pullback. No reducedness or smoothness
of Y is needed. Empty curves and V = C give the same argument with empty support. -/
theorem injective_brauer_pullback_finite_modification {k : Type u} [Field k]
    [IsAlgClosed k] {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsReduced C] (ν : Y ⟶ C) [IsFinite ν] (V : C.Opens) (hV : Dense (V : Set C))
    [IsIso (ν ∣_ V)] :
    Function.Injective (fun x : C.CohomologicalBrauerGroup ↦
      Sheaf.H.map (Scheme.upperStarGmSheafToGmSheaf ν) 2
        (Etale.cohomologyMap ν C.gmSheaf 2 x)) := by
  sorry

end AlgebraicGeometry.IsCurve
