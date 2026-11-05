/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedRecollement

/-!
# Open-closed localization for relative etale compact support

Source: Stacks Project, Tag 0GKP, `lemma-relative-triangle-associated-to-open`
(blueprint: lem-weil-pbc-etale-compact-support-open-closed-triangle).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
