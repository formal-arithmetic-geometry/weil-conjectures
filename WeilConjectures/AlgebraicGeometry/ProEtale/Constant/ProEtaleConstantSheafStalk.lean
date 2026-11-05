/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Mathlib.CategoryTheory.Limits.Connected
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSheafificationGeometricStalk

/-!
# Stalks of constant module sheaves on the pro-etale site

Source: Bhatt--Scholze, The pro-etale topology for schemes, Sections 6.5 and 6.8;
Stacks Project, Tags 0F6B, 0F6C, 00Y8(3), and 03CY
(blueprint: lem-weil-proetale-constant-sheaf-stalk).

The additive germ map is specified by the actual sheafification unit and the
coprojection at `(Y,y)`. Scalar compatibility uses the constant-ring germ map;
thus bijectivity expresses an isomorphism over the original coefficient ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

end AlgebraicGeometry.Scheme
