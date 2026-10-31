/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.ModuleCupGodementRelations
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.RingComplexGodementModelMapsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Functorial maps of the concrete Godement ring complex -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] ringComplexGodementModel ringComplexGodementUnit
  ringComplexGodementResolution resmap

private abbrev pt : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

end
end AlgebraicGeometry
