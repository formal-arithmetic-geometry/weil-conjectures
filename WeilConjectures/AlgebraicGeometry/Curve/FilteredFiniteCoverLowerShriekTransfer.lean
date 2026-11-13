/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore
import WeilConjectures.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract

/-! # Transfer from a filtered finite etale cover through extension by zero

Source: Stacks Project, proof of 03SD, paragraphs 2--4.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsCurve

/-- Transfer the constant case using a given finite etale cover, filtration and retraction.

Source: Stacks Project, 03SD, paragraphs 2--4. -/
theorem filteredFiniteCoverLowerShriekTransfer {k : Type u} [Field k] [IsAlgClosed k]
    {X U V : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    (n : ℕ)
    (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (ι : ∀ i, W i ⟶ W (i + 1)) (hzero : IsZero (W 0))
    (hend : Nonempty (W n ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))
    (hquot : ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
      (constantSheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))
    (ρ : (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G) ⟶ G)
    (hρ : (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).unit.app G ≫ ρ = 𝟙 G)
    (hconstant : ∀ {Y T : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g] [IsReduced Y]
      (a : T ⟶ Y) [IsOpenImmersion a],
      IsCurve.Assertions (ULift.{u + 1} (ZMod r)) g
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) a).obj
          ((constantSheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod r)))))) :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj G) := by
  apply filteredFiniteCoverLowerShriekTransfer_retract f j r G v
    (filteredFiniteCoverLowerShriekTransfer_core f j r G v n W ι hzero hend
      hquot hconstant) ρ hρ

end AlgebraicGeometry.IsCurve
