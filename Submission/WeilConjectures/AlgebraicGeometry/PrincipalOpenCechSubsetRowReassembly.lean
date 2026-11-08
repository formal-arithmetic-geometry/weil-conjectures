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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Reassembly of one ordered Čech row

Source: Stacks Project, Tags 08C1, 08C0, and 01FG.
(blueprint: lem-sc-principal-open-cech-subset-row-reassembly).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance] Classical.propDecidable

private theorem sum_apply {M N : AddCommGrpCat.{u}} {ι : Type*}
    (g : ι → (M ⟶ N)) (s : Finset ι) (x : M) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv g s) x)

end AlgebraicGeometry
