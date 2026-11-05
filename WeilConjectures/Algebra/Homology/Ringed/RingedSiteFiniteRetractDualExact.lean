/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Internal dual and exact Hom of a finite-free retract

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final finite-free/direct-summand
calculation, expanded in the node into dual-basis and kernel/epimorphism calculations
(blueprint: lem-sfb-ringed-site-finite-retract-dual-exact).

The coefficient universe contains both site universes, without equating them. All maps
below use the existing internal Hom. The bidual isomorphism is specified by evaluation
on every object of every slice, and its inverse by the finite dual-basis formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe c v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v w}]
  {R : Sheaf J CommRingCat.{max c v w}}

attribute [local instance 2000] ModuleCat.isAddCommGroup ModuleCat.isModule
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize SheafOfModules.instPreadditive

namespace FiniteRetractProof

variable (R)

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{max c v w})).obj R

variable {R}

end FiniteRetractProof

open FiniteRetractProof

-- Keep coordinate constructions folded when elaborating the public interface.
attribute [local irreducible] finiteRetractCoordinate finiteRetractVector finiteRetractCovector

-- The public statement uses the library's original instances.
attribute [-instance] proofAbelian proofHomContraAdditive
  proofHasFiniteBiproducts proofSectionModule proofHomPreservesZero

end SheafOfModules
