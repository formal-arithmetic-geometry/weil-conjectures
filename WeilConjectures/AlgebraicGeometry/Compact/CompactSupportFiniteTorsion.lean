/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonIso
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonComposition

/-!
# Compact-support base change with finite coefficients and arbitrary refinements

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-torsion;
Stacks Project, Tags 0DDE, 0F7I, 0F7J and 0F7F (blueprint: thm-cbc-finite-torsion).

The exchange map, its invertibility, identity and horizontal pasting, and its canonical
compactification-independent version and vertical pasting already exist upstream. The theorem
below also identifies the comparisons specified by the node with the canonical comparisons
for every proper refinement, including refinements whose square over the open is not Cartesian.
Together with the recorded upstream declarations, this states all clauses of the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Retain the chosen-resolution interfaces while elaborating the private proofs.
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryPlus
  CategoryTheory.Functor.rightDerivedFunctorPlus lowerStar upperStar
  properOpenComparison properOpenIdentification
  CategoryTheory.Functor.rightDerivedFunctorPlusCompIso' properOpenDirectImageCompIso

end AlgebraicGeometry.Etale
