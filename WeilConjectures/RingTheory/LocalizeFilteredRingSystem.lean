/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RingHom.EssFiniteType
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime

/-! # Localizing a filtered ring system at a local target

Source: Stacks Project, Algebra, Tags 037D and 00QV.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingHom

end RingHom
