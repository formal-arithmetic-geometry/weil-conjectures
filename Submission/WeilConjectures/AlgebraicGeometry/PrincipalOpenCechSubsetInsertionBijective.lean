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
import Mathlib.Algebra.Category.ModuleCat.Products

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Properties of explicit subset insertion

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem sum_apply {M N : AddCommGrpCat.{u}} {ι : Type*}
    (f : ι → (M ⟶ N)) (s : Finset ι) (x : M) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv f s) x)

end AlgebraicGeometry
