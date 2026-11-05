/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Fixed.FixedExponentDerivedCoproducts
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorDirectSums
import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration

/-!
# Constant-module projection for bounded torsion objects

Source: Stacks Project, Tag 0F12, `lemma-pull-out-constant-mod-n`, relative fixed-exponent
extension; and the docstring of `torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing`
in `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage`
(blueprint: lem-sf-projection-torsion-object-constant).

The map is the existing counit mate, a natural transformation of bifunctors. Its target
is identified with `Rf_*(E ⊗ᴸ M_X[0])` by the canonical constant inverse-image isomorphism.
The statement concerns the uncompleted tensor in the ordinary unbounded derived category.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
