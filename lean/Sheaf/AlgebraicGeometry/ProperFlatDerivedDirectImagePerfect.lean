/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage

/-! # Perfect direct image for proper flat finitely presented morphisms

Source: Stacks Project, Tag 0B91, Lemma 36.30.4(1).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Proper flat finitely presented pushforward takes perfect complexes to perfect complexes.
Source: Stacks Project, Tag 0B91, Lemma 36.30.4(1), deduced from Tag 0A1H.
(blueprint: lem-sc-proper-flat-derived-direct-image-perfect-universes).

Proof: Work in the standard K-injective derived models on X, Y and their opens.
Localization equivalences identify these models with the supplied ones; exact restriction
commutes with these equivalences, so local strictly perfect representatives, and hence
perfectness, are preserved and reflected. Derived direct image commutes with the same
localization equivalences by its K-injective computation. In a common large Hom universe,
apply properSupport_perfect_directImage to E and the complex consisting of O_X in degree
zero. This complex is bounded and termwise finitely presented; its nonzero term is flat
over Y by flatness of f and has proper support by properness of f. The zero terms satisfy
all the conditions as well. The derived tensor unit identifies E tensor O_X with E,
so the first conclusion is that Rf_*E is perfect. Transport this conclusion back along
the localization equivalences on Y and its opens. This argument needs no right adjoint
or compactness assumption and works for different ambient Hom universes. For an empty
scheme or the zero perfect complex the same tensor-unit and support arguments apply. -/
theorem properFlat_derivedDirectImage_perfect
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj E) := by sorry

end AlgebraicGeometry
