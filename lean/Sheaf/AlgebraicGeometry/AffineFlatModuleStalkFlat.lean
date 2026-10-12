/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat

/-! # Flat stalks from flat sections on affine subopens

Source: Stacks Project, Modules Tag 05NE, Algebra Tags 00H9 and 00HT.
(blueprint: lem-pc-affine-flat-module-stalk-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flat sections on all affine subopens give flatness of an individual stalk.
Source: Stacks Project, Modules Tag 05NE; Algebra Tags 00H9 and 00HT.
(blueprint: lem-pc-affine-flat-module-stalk-flat).

Proof: Choose an affine neighbourhood V of x. The affine neighbourhoods U of x
contained in V form a filtered basis: intersections are open, and each neighbourhood
contains an affine neighbourhood of x. Restrict scalars on G(U) along O(V) -> O(U).
The hypothesis gives flatness over O(V) for every such U. Germ maps identify their
filtered colimit with G_x as an O(V)-module; this uses only the neighbourhood-basis
property, not quasi-coherence. Filtered colimits of flat modules are flat (Tag 00H9).
The ring O_x is the localization of O(V) at the prime corresponding to x. The
O(V)-action just constructed is restriction of the canonical O_x-action, by the
formula for multiplication of germs. For a module over a localization, flatness over
the original ring is equivalent to flatness over the localization (Tag 00HT).
Consequently G_x is flat over O_x. There is no point to consider on the empty scheme;
for the zero sheaf this argument gives the zero, hence flat, stalk module. -/
theorem flat_stalk_of_affineFlatOver_identity {Y : Scheme.{u}} (G : Y.Modules)
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y)) (x : Y) :
    Module.Flat (Y.toRingedSpace.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj G) := by sorry

end AlgebraicGeometry
