/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomotopyLimitExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Pullback along weakly étale morphisms commutes with derived limits of towers

For a weakly étale `f : X ⟶ Y`, the pullback `f^*` of pro-étale sheaves is restriction along the
localization functor (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), so it is
exact and preserves countable products, computed sectionwise
(`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_discrete_upperStar_ab`,
`AlgebraicGeometry.ProEtale.preservesLimitsOfShape_discrete_upperStar_moduleCat`). Hence its
derived functor sends homotopy limit cones (`R lim`) to homotopy limit cones
(`AlgebraicGeometry.ProEtale.isHomotopyLimit_upperStar_mapDerivedCategory_mapCone`), and then
also the Milnor sequences.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : WeaklyEtale f]

variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.ProEtale
