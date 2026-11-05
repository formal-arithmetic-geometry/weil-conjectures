/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.CategoryTheory.SixFunctors.IndHeartRealization
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Constructible sheaves are finitely presented and realize the ind-heart fully faithfully

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`det-ind-heart-full-faithfulness` (blueprint: det-ind-heart-full-faithfulness).

The coefficient ring objects carry their canonical ring-object structures: the one of
`Profinite.continuousMapRingObj E` resp. `Profinite.padicAlgClRingObj ℓ`, and on
`Λ_X = condensedRingObj Λ X` the one transported along `upperStarFromPoint X` (the scoped
instance `Functor.monObjObj` of `CategoryTheory.Obj`). Small diagrams are indexed by categories
in `Type (u + 1)`, the hom universe of the module category, as in `CategoryTheory.Ind`
(size convention def-weil-size-convention).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
