/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.SixFunctors.BaseChange.Derived
import Submission.WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Submission.WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Composition and identity of proper-open comparison maps

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-proper-open-comparison-composition, order 1842
(blueprint: lem-weil-pbc-proper-open-comparison-composition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Naturality and the right triangle turn conjugate unit equations into counit equations.
-- The canonical restriction map, expressed entirely through the derived counit.
private noncomputable def restriction
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : D ⥤ E} {R : E ⥤ D} (adj : F ⊣ R)
    (U : E ⥤ C) (V : D ⥤ C) (k : V ≅ F ⋙ U) :
    R ⋙ V ⟶ U where
  app M := k.hom.app (R.obj M) ≫ U.map (adj.counit.app M)
  naturality {M N} b := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [reassoc_of% k.hom.naturality (R.map b)]
    rw [← U.map_comp, adj.counit_naturality, U.map_comp]
    exact (Category.assoc _ _ _).symm

-- Associativity of pullback and the conjugate counit equation give composition of restriction.
-- The adjunction calculation applies to any natural restriction maps with these normalizations.
end AlgebraicGeometry.Etale
