/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Synchronizing the two local rank conditions

Source: Stacks Project, Tag 0BDP, rank decomposition and the two rank-r loci.
(blueprint: lem-sc-picard-universal-rank-match-conjunction).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The two single-image conditions give the common-neighbourhood condition.
Source: Stacks Project, Tag 0BDP, first and third proof paragraphs: both loci
use the rank fixed by E, not independent ranks inferred from the direct images.
(blueprint: lem-sc-picard-universal-rank-match-conjunction).

Proof: Fix a further base change h and a point t. Choose neighbourhoods U
and V and witness ranks r and s for the two single-image conditions. Set W=U∩V;
it contains t. Restriction by the inclusions W→U and W→V preserves finite local
freeness of fixed rank. The composition isomorphisms for tensor pullback, and
canonical maps between the corresponding fibre products, identify the two
restrictions of E with its pullback to X_W. The structure-sheaf unit hypothesis
on the residue-field base change at t implies that its fibre is nonempty.
Indeed an empty fibre would have zero structure sheaf, contradicting that
its direct image is the nonzero residue-field structure sheaf. Choose a point;
its stalk of E has both ranks r and s, and local
rings are nontrivial, so invariant basis number gives r=s. The two direct images
restricted to W and E on X_W therefore all have the same rank r. This gives the
common witness required in PicardUniversalRankMatch. The argument repeats for
every h and t. If the test scheme is empty there is no t to check, and rank zero
causes no exception to invariant basis number. -/
theorem picardUniversalRankMatch_of_singleRankMatch {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hE : PicardUniversalSingleRankMatch f E E g)
    (hdual : PicardUniversalSingleRankMatch f E (Modules.dual E) g) :
    PicardUniversalRankMatch f E g := by sorry

end AlgebraicGeometry.Scheme
