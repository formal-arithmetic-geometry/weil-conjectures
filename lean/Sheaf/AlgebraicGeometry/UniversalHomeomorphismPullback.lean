/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-!
# Universal-homeomorphism pullback coherence

Source: Stacks Project, Tags 04DZ and 03SI.
-/

set_option linter.style.haveILetI false
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tags 04DZ and 03SI, base-change coherence.
Proof: Stability of universal homeomorphisms under base change makes pullback.fst g u a universal
homeomorphism. Apply topological invariance to it: its additive upperStar is an equivalence, so
the unit and counit of upperStarLowerStarAdjunction are isomorphisms, and cohomologyMap_bijective
gives the asserted cohomology bijections.
Construct set-valued inverse-image compositors by comparing composite sheaf pullback adjunctions
using lowerStarComp and leftAdjointUniq. Equivalently use the repaired comparison to inverse sheaf
equivalences on the universal-homeomorphism sides. Compose the inverse compositor for pullback.snd
g u followed by u with the compositor for pullback.fst g u followed by g, identifying the total
morphisms by pullback.condition. This gives the set-valued square isomorphism; upperStarComp gives
the additive square isomorphism in the same way.
For a sheaf F on X', insert the inverse counit F → u^*u_*F and apply s^*, where s = pullback.snd g
u. Use the inverse-image square s^*u^* ≅ p^*g^*, where p = pullback.fst g u, then apply p_* and
cancel p_*p^* by the inverse unit. This constructs p_*s^*F ≅ g^*u_*F, naturally in F, which is the
displayed mixed square isomorphism. Every arrow is invertible by topological invariance for u and
p. Perform this construction both for sets (using the repaired comparison) and for additive
sheaves.
Apply the composition clause of cohomologyPullbackFunctorial to both paths in the pullback square.
Apply Sheaf.H.map of the respective inverse upperStarComp to cancel each forward compositor. The
two results are pullback along the common composite, identified by pullback.condition, so they are
equal as asserted.
(blueprint: thm-weil-pbc-universalHomeomorphism_pullback) -/
theorem universalHomeomorphism_pullback {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    ∀ (Y : Scheme.{u}) (g : Y ⟶ X),
      IsUniversalHomeomorphism (pullback.fst g u) ∧
      IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.fst g u)).unit ∧
      IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (pullback.fst g u)).counit ∧
      (∀ (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
        Function.Bijective (cohomologyMap (pullback.fst g u) G q)) ∧
      Nonempty (Scheme.etaleSetPullback u ⋙ Scheme.etaleSetPullback (pullback.snd g u) ≅
        Scheme.etaleSetPullback g ⋙ Scheme.etaleSetPullback (pullback.fst g u)) ∧
      Nonempty (Scheme.etaleSetPullback (pullback.snd g u) ⋙
        lowerStar (Type (u + 1)) (pullback.fst g u) ≅
          lowerStar (Type (u + 1)) u ⋙ Scheme.etaleSetPullback g) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} u ⋙
        upperStar AddCommGrpCat.{u + 1} (pullback.snd g u) ≅
          upperStar AddCommGrpCat.{u + 1} g ⋙
            upperStar AddCommGrpCat.{u + 1} (pullback.fst g u)) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} (pullback.snd g u) ⋙
        lowerStar AddCommGrpCat.{u + 1} (pullback.fst g u) ≅
          lowerStar AddCommGrpCat.{u + 1} u ⋙ upperStar AddCommGrpCat.{u + 1} g) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
        (x : Sheaf.H F q),
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (pullback.snd g u) u
            (pullback.fst g u ≫ g) (pullback.condition (f := g) (g := u))).inv.app F) q
          (cohomologyMap (pullback.snd g u) ((upperStar AddCommGrpCat.{u + 1} u).obj F) q
            (cohomologyMap u F q x)) =
        Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (pullback.fst g u) g).inv.app F) q
          (cohomologyMap (pullback.fst g u) ((upperStar AddCommGrpCat.{u + 1} g).obj F) q
            (cohomologyMap g F q x)) := by
  sorry
end AlgebraicGeometry.Etale
