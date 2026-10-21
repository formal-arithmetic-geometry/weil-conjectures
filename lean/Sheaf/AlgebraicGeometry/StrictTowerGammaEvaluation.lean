/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SingleProperOpenArrows
import Sheaf.AlgebraicGeometry.StrictTowerAlphaEvaluation
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange

/-!
# Evaluation of the proper mate

Source: Stacks Project, Tags 07A7 and 0F7B, adjunction mate calculus.
(blueprint: lem-cbc-strict-tower-gamma-single-evaluation)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

/-- Evaluation of the proper mate follows from evaluation of alpha and the two
specified direct-image evaluation mates.
Source: Stacks Tags 07A7 and 0F7B
(blueprint: lem-cbc-strict-tower-gamma-single-evaluation).
Proof: apply coefficient/exchange mate pasting to the alpha evaluation square.
The two push comparisons are exactly the mates of evalG inverses, and both gamma
maps are proper-adjunction mates. Their counit equations give all four side faces
of the mate cube. -/
theorem gamma_single_evaluation (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived B V) (n : ℕ) :
    (evalJ B i n).hom.app ((R B r).obj M) ≫
        (moduleJ B i).mapDerivedCategory.map ((evalR B r n).app M) ≫
        (singleGamma B k r p i h).app ((ev B V n).obj M) =
      (ev B T n).map ((gamma B k r p i h).app M) ≫
        (evalR B p n).app ((J B k).obj M) ≫
        (moduleDirectImage B p).rightDerivedFunctor.map ((evalJ B k n).hom.app M) := by
  let ar : (modulePullback B r).mapDerivedCategory ⊣
      (moduleDirectImage B r).rightDerivedFunctor :=
    (Scheme.proEtaleRingModuleAdjunction r (coefficients B S)
      (coefficients B V) (constantRingIso B r)).mapDerivedCategoryRightDerivedAdjunction
  let ap : (modulePullback B p).mapDerivedCategory ⊣
      (moduleDirectImage B p).rightDerivedFunctor :=
    (Scheme.proEtaleRingModuleAdjunction p (coefficients B T)
      (coefficients B W) (constantRingIso B p)).mapDerivedCategoryRightDerivedAdjunction
  exact Adjunction.coefficient_exchange_of_counit (adj B r) (adj B p) ar ap
    (alpha B k r p i h) (singleDerivedAlpha B k r p i h)
    (gamma B k r p i h) (singleGamma B k r p i h)
    (fun K ↦ mateEquiv_counit (adj B r) (adj B p) (alpha B k r p i h) K)
    (fun K ↦ mateEquiv_counit ar ap (singleDerivedAlpha B k r p i h) K)
    (evalG B r n) (evalG B p n) (evalJ B i n).hom (evalJ B k n).hom
    (evalR B r n) (evalR B p n)
    (fun K ↦ mateEquiv_counit (adj B r) ar (evalG B r n).inv K)
    (fun K ↦ mateEquiv_counit (adj B p) ap (evalG B p n).inv K)
    (fun K ↦ alpha_single_evaluation B k r p i h K n) M

end AlgebraicGeometry.ProEtale.StrictTower
