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
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
import WeilConjectures.AlgebraicGeometry.AbelianVariety.ModuleCupGodementRelations
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Localization coordinates of the ordered Čech fibre

Source: Stacks Project, Tag 099D(d), Cohomology, ordered Čech complexes.
(blueprint: lem-weil-pbc-ring-complex-ordered-cech-coordinates)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
namespace AlgebraicGeometry

noncomputable section

private def signs (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (q : ℕ) : M ≃ₗ[A] M :=
  (LinearEquiv.neg A) ^ (q + 1)

end
end AlgebraicGeometry
