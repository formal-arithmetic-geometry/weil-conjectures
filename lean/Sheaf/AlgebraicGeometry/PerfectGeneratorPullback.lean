/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C1, Z5
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectGeneratorPullback
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization

/-! # Affine pullback of a perfect generator

The adopted source theorem `AlgebraicGeometry.perfect_generator_pullback` also asserts
perfectness of the pullback. This module re-exports it and retains the earlier generator
criterion as `AlgebraicGeometry.perfect_generator_pullback_compat`, with its original
hypotheses. In particular no localization family on the source scheme is assumed.

Source: Stacks Project, perfect.tex, Tag 0BQT.
(blueprint: lem-pc-perfect-generator-pullback).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The original generator criterion for affine pullback, without an explicit family of
localizations on opens of the source scheme.
Source: Stacks Project, perfect.tex, Tag 0BQT
(blueprint: lem-pc-perfect-generator-pullback).

Proof: `nonempty_derivedOpenLocalization` supplies the localization family in the same
Hom universe on all opens of X'. Apply the adopted affine pullback theorem and retain
its quasi-coherence and generator conjuncts. Its proof uses the derived adjunction and
shift compatibility to transfer Hom vanishing to direct image, whose quasi-coherence
comes from the affine derived equivalence. The generator on X makes direct image zero;
affine conservativity then makes the original object zero. Empty schemes and zero
objects require no extra assumptions. -/
theorem perfect_generator_pullback_compat {X X' : Scheme.{u}}
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
  obtain ⟨hX'⟩ := nonempty_derivedOpenLocalization.{u, w} X'
  let := hX'
  exact (perfect_generator_pullback g M hperfect hgen).2

end AlgebraicGeometry
