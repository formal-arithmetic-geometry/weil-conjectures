/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine pullback of a perfect generator

Source: Stacks Project, Derived Categories of Schemes, Remark 36.16.4, Tag 0BQT
(blueprint: lem-pc-perfect-generator-pullback).

The weak generator condition is expressed by the shifted-Hom vanishing criterion,
just as in `AlgebraicGeometry.exists_perfect_generator`. All test objects belong to
`D_QCoh`, while the Hom groups and shifts are computed in the ambient derived category.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The derived pullback of a perfect generator along an affine morphism of qcqs schemes
is a generator of the quasi-coherent derived category of the source.
Source: Stacks Project, Tag 0BQT (blueprint: lem-pc-perfect-generator-pullback).

Proof:
1. By `lem-pc-derived-pullback-tensor-qcoh`, derived pullback preserves quasi-coherent
cohomology. The adjunction `lem-pc-ringed-spaces-derived-adjoint-general` restricts to
quasi-coherent derived categories: `lem-sc-finite-affine-derived-equivalence` ensures
that affine derived pushforward preserves quasi-coherent cohomology. Thus shifted Hom
from the pullback of M to E agrees with shifted Hom from M to the derived pushforward of E.
2. If all the former Hom groups vanish, so do the latter. The generator hypothesis on M,
namely the zero-detection criterion of `def-pc-generators`, gives Rg_*E = 0.
3. By `lem-sc-affine-derived-pushforward-conservative`, affine derived pushforward reflects
isomorphisms. Apply this to 0 → E to deduce E = 0. Conversely, Hom into a zero object
vanishes. This is precisely the generator criterion on the source. -/
theorem perfect_generator_pullback {X X' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (g : X' ⟶ X) [IsAffineHom g] (M : schemeDerivedQCohCategory X)
    (hperfect : Scheme.IsPerfect X M.obj)
    (hgen : ∀ E : schemeDerivedQCohCategory X,
      IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (M.obj⟦n⟧ ⟶ E.obj)) :
    schemeDerivedQCohProperty X' ((derivedPullback g).obj M.obj) ∧
      ∀ E : schemeDerivedQCohCategory X',
        IsZero E.obj ↔ ∀ n : ℤ,
          Subsingleton (((derivedPullback g).obj M.obj)⟦n⟧ ⟶ E.obj) := by
  sorry

end AlgebraicGeometry
