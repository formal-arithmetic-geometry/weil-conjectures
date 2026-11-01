/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedRefinement.RingedRefinementData
/-! The separate cartesian and clopen factors of finite refinement.
(blueprint: new-def-pur-ringed-refinement-finite-factors). -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement
attribute [local irreducible] ProEtale.StrictTower.G ProEtale.StrictTower.J
  ProEtale.StrictTower.gComp ProEtale.StrictTower.jComp ProEtale.StrictTower.jCongr
  ProEtale.StrictTower.pi ProEtale.StrictTower.gId ProEtale.StrictTower.beta

/-- The cartesian strict-tower comparison for the specified pullback shape.
Source: Stacks 0F7B; coefficient supplement Step 10.
(blueprint: new-def-pur-ringed-refinement-finite-factors). -/
def finiteTowerBeta {T : Scheme.{u}} (B : Type (u + 1)) [CommRing B]
    {X Y Z : Over T} {u : Y ⟶ Z} {j₁ : X ⟶ Y} {j₂ : X ⟶ Z}
    [IsOpenImmersion j₂.left] (d : Shape u j₁ j₂) :
    ProEtale.StrictTower.J.{u} B j₂.left ⋙ ProEtale.StrictTower.G.{u} B u.left ≅
      ProEtale.StrictTower.G.{u} B d.q.left ⋙ ProEtale.StrictTower.J.{u} B d.b.left :=
  ProEtale.StrictTower.beta B d.q.left d.b.left j₂.left u.left
    (congrArg (fun f ↦ f.left) d.pullback.w).symm d.schemePullback.flip

set_option maxHeartbeats 2000000 in
-- Elaborating the compositor word compares several nested functor compositions.
end SheafOfModules.RingedRefinement
