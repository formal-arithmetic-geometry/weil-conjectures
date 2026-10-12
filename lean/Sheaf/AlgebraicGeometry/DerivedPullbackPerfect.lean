/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback

/-! # Derived pullback preserves perfect complexes

Source: Stacks Project, perfect.tex, Tag 09UA.
-/

@[expose] public section

universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- Derived pullback of a perfect complex is perfect.
Source: Stacks Project, perfect.tex, Tag 09UA
(blueprint: lem-pc-derived-pullback-perfect).
Proof: for a point t of T, choose a neighbourhood U of g(t) on which E is represented
by a strictly perfect complex P. Restriction commutes with derived pullback, so over
the inverse image of U its pullback is represented by the termwise pullback of P,
by `flatComplexDerivedPullback`: finite projective modules are flat and P is bounded.
The termwise pullback is bounded and each term remains a direct summand of a finite
free module, since pullback preserves finite free modules and the equation defining
that summand. This gives the strictly perfect neighbourhood required at t. The argument
also applies to the empty scheme and to zero complexes. -/
theorem derivedPullback_preserve_perfect {T X : Scheme.{u}} (g : T ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect T ((derivedPullback g).obj E) := by sorry

end AlgebraicGeometry
