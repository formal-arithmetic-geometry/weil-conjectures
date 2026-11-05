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
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.Algebra.Homology.DerivedTensor

/-!
# Derived tensor product on the small pro-etale site

Source: the Weil conjectures blueprint, `def-weil-derived-tensor`, order 663;
Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU
(blueprint: def-weil-derived-tensor).

The constant sheaf is formed in commutative rings before forgetting to rings,
so the recorded K-flat predicate and sheaf tensor product apply directly.
-/

@[expose] public section

universe w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{w}) (A : Type w) [CommRing A]

set_option hygiene false in
set_option quotPrecheck false in
local notation "𝓡" =>
  (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} A))
set_option hygiene false in
set_option quotPrecheck false in
local notation "𝓢" =>
  (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj 𝓡

end AlgebraicGeometry.Scheme
