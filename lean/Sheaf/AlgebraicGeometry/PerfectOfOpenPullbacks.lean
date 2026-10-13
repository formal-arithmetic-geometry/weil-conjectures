/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
/-! # Perfectness detected on open neighbourhoods

Source: Stacks Project, Tag 08CM, definition-perfect
(blueprint: lem-pc-perfect-of-open-pullbacks).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Perfectness is local for derived pullback along open immersions.
Source: Stacks Project, Tag 08CM, definition-perfect; Tag 0A1H, locality sentence.
Proof: for x choose U containing x on which the derived restriction is perfect.
Choose a strictly perfect representative near the point of U corresponding to x.
An open of U is an open V of S contained in U. Exact open restriction agrees with
its left derived functor, by uniqueness of left derived functors. The equivalences
between module sheaves on open subschemes and on localized sites identify successive
restrictions with restriction to V. They preserve finite free modules, their retract
maps and zero terms. Transport the local representative and its isomorphism across
these equivalences. This gives precisely the witness at x in S.IsPerfect K.
The empty scheme is vacuous and no uniform bound or quasi-compactness is required.
(blueprint: lem-pc-perfect-of-open-pullbacks). -/
theorem perfect_of_open_pullbacks
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {S : Scheme.{u}} (K : schemeDerivedCategory S)
    (h : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧
      Scheme.IsPerfect U.toScheme ((derivedPullback U.ι).obj K)) :
    Scheme.IsPerfect S K := by sorry

end AlgebraicGeometry
