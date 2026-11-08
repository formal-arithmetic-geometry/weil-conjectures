/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Submission.WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Submission.WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.Data.Finset.Sort
import Submission.WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetRowReassembly
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Horizontal differential of explicit subset insertion

Source: Stacks Project, Tag 08C1 and equation (20.40.0.1) (Tag 08C0),
and Tag 01FG, ordered-complex differential preceding Definition 20.23.2.
(blueprint: lem-sc-principal-open-cech-subset-insertion-horizontal).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem sum_apply {α : Type*} [Fintype α]
    {G H : AddCommGrpCat.{u}} (F : α → (G ⟶ H)) (x : G) :
    (∑ i, F i) x = ∑ i, F i x := by
  change (AddCommGrpCat.homAddEquiv (∑ i, F i)) x = _
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rfl

end AlgebraicGeometry
