/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
import WeilConjectures.AlgebraicGeometry.FreeComplexMapsToResolution
import WeilConjectures.RingTheory.TorIdealConnectingFormula
import WeilConjectures.RingTheory.TorIdealComparisonCompatibility
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Naturality of the ideal-kernel description of first Tor

Source: Stacks Project, Algebra, Tags 00M6, 00M5, 00MO and 00LS
(blueprint: lem-weil-pbc-tor-ideal-kernel-naturality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators

namespace ModuleCat

end ModuleCat
