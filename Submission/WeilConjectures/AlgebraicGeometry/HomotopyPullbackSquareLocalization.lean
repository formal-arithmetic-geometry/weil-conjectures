/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

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

private theorem homotopy_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (M : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).inv.app M =
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app M := by
  rfl


end
end AlgebraicGeometry
