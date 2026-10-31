/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction

/-! # Normalization of the projective-bundle pullback section

Source: Stacks Project, Sheaves, Tags 0095 and 0096.
(blueprint: lem-pur-projective-bundle-pullback-section-normalization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The pullback section used in the projective-bundle generator formula is exactly the
section represented by the pure tensor 1 tensor m.
Source: Stacks Project, Tags 0095 and 0096.
Proof: the adjunction chosen in the projective-bundle convention is chosen from the theorem
whose second component specifies precisely this pure-tensor unit formula. Evaluating that
component on the given section proves the equality, including on empty opens and zero modules.
(blueprint: lem-pur-projective-bundle-pullback-section-normalization). -/
theorem projectiveBundlePullbackSection_eq_tensorPullbackSection
    {X Y : Scheme.{u}} (g : X ⟶ Y) {F : Y.Modules} {U : Y.Opens} (m : Γ(F, U)) :
    projectiveBundlePullbackSection g m = Scheme.Modules.tensorPullbackSection g F U m := by
  exact (Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction g)) F (op U) m

end AlgebraicGeometry
