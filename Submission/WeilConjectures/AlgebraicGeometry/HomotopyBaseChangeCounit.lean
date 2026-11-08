/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.HomotopyPullbackSquareLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Localization of the canonical homotopy pullback square

Source: Stacks Project, Tags 0D5S and 0DVC.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section


private noncomputable abbrev adj {A B : Scheme.{u}} (k : A ⟶ B) :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)


end
end AlgebraicGeometry
