/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Data.Int.Interval

/-! # Local algebraicity of maps between bounded constant module complexes -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [CommRing R]
  [HasSheafify J (ModuleCat.{w} R)] [J.WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, HasSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).WEqualsLocallyBijective (ModuleCat.{w} R)]
  [∀ V : C, (J.over V).HasSheafCompose (forget (ModuleCat.{w} R))]
  [(constantSheaf J (ModuleCat.{w} R)).Additive]
  [∀ V : C, (constantSheaf (J.over V) (ModuleCat.{w} R)).Additive]
  [∀ V : C, (J.overPullback (ModuleCat.{w} R) V).Additive]

end CategoryTheory
