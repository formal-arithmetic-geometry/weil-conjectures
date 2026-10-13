/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Perfection of the direct image of a relatively flat single module

Source: Stacks Project, Tag 0B91(2), via the proof of Tag 0A1H.
(blueprint: lem-pc-proper-flat-single-derived-direct-image-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wS

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper direct image of a finitely presented, relatively flat module is perfect.
This statement has no Čech cover, specified section model or base-change conclusion.
Source: Stacks Project, Tag 0B91(2), using Tag 0A1H.
(blueprint: lem-pc-proper-flat-single-derived-direct-image-perfect).

Proof: work locally on an affine base Spec A. Express A as a filtered colimit of
finitely generated Z-algebras. Finite presentation spreads out X and F to a
Noetherian stage; enlarge the stage so the morphism is proper and the module is
flat over that stage. On this Noetherian stage proper coherence gives bounded
coherent direct-image cohomology. Relative flatness gives finite relative Tor
amplitude for the single module, and proper pushforward preserves the resulting
finite Tor dimension. Bounded coherent cohomology and finite Tor dimension give
a perfect direct image there. The relatively flat cohomology-and-base-change
comparison identifies its derived pullback with the direct image over A. Pulling
back a local bounded finite-projective representative gives a strictly perfect
representative on the base. Glue the local witnesses. This is the specialization
E=O_X and G=F[0] of the argument of 0A1H used in 0B91(2), and requires no flatness
of f itself. Compute and transport the direct image by localization uniqueness
so these witnesses lie in the supplied source, base and open-site localizations;
no family of localizations for all schemes is assumed. Empty schemes and the
zero module give the zero strictly perfect representative. -/
theorem properFlat_single_derivedDirectImage_perfect
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (F : X.Modules) [F.IsFinitePresentation] (hF : F.IsFlatOver f) :
    S.IsPerfect ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) := by sorry

end AlgebraicGeometry
