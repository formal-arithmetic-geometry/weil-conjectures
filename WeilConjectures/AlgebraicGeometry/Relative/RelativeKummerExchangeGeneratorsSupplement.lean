/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGenerators

/-!
# Exchange on normalized global generators

Source: blueprint main-20261015, sk-prop-a1-kummer,
prop-pur-gm-relative-kummer.proof.md, Step 3; Stacks Tags 0736 and 072W
(blueprint: lem-pur-relative-kummer-exchange-generators).

Global classes are derived morphisms out of the constant free rank-one module sheaf.
Sections are sheaf morphisms out of that same sheaf, equivalently their value on 1.
All comparisons below are the canonical single, constant, shift and adjunction comparisons.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Generic
variable (C : Type u') [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  (M : C)

end Generic

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStar lowerStar

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true

end AlgebraicGeometry.Etale
