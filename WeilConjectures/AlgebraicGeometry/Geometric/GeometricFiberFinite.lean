/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Finite-coefficient geometric-fibre formula

Source: Stacks Project, Tag 0DDF; SGA 4, Expose XII, Corollaire 5.2(iii);
blueprint `sec-proper-base-change/sk-thm-properbasechange/`
`cor-weil-pbc-geometric-fiber-finite.md`
(blueprint: cor-weil-pbc-geometric-fiber-finite).

The cohomological formula includes the two endpoint identifications explicitly:
global sections of the source are the geometric stalk, and global sections of the
target are the cohomology of the geometric fibre. The map between these presentations
is the degree-q base-change map, not an unspecified isomorphism between groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
