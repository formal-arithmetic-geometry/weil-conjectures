/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import WeilConjectures.CategoryTheory.TorsionSheafConstantModule
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf

/-! # Roots of unity on the small pro-etale site

Source: Stacks Project, Section 59.28, Tag 03PK; Definition 59.23.1, Tag 03P4
(blueprint: def-pur-roots-of-unity-sheaf).

The power map, kernel, constant-ring module and transition maps use the original
sectionwise global-sections rings. No invertibility hypothesis on the exponent is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
