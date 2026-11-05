/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDerivedProductRepresentation
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.DeligneLaumon.SequentialDerivedInverseLimit
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Mittag--Leffler vanishing for finite abelian groups

Source: blueprint sec-deligne-laumon-a1/sk-l-dl-a1-endpoints, order 2731;
Stacks Project, Tags 07KW and 07KY (blueprint: lem-weil-pbc-mittag-leffler).
The natural index n denotes positive level n+1. Canonical maps in D(Ab) are specified
by their limit-projection equations, exactly as in `milnor_shortExact`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
