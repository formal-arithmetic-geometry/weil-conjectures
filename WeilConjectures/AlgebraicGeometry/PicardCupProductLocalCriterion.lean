/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCupProductMap
import WeilConjectures.AlgebraicGeometry.PicardCounitEqualRanks
import WeilConjectures.AlgebraicGeometry.PicardCupProductSplitCounit
import WeilConjectures.AlgebraicGeometry.PicardCupProductOfCounit
import WeilConjectures.AlgebraicGeometry.PicardPullbackPerfectPairing

/-! # The local dual-basis criterion for degree-zero cup product

## References

* Stacks Project, Tag 0BDP.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a single base, cup product detects the evaluation counit when the direct image
and the bundle have the same local rank. Neither properness nor flatness nor universal
base-change compatibility is an assumption of this local calculation. (Stacks, Tag 0BDP) -/
theorem picardCupProduct_isIso_iff_counit_of_local_ranks
    {X S W : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) [E.IsFiniteLocallyFree]
    (j : W ⟶ S)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hN : ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj E)).IsFiniteLocallyFree)
    (hRanks : ∀ w : W, ∃ U : W.Opens, w ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f j)).obj
            ((Modules.tensorPullback (pullback.fst f j)).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ j))).obj E) r) :
    IsIso (picardCupProductMap f E j hO) ↔
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).counit.app
          ((Modules.tensorPullback (pullback.fst f j)).obj E)) := by
  let p := pullback.snd f j
  let q := pullback.fst f j
  let M := (Modules.tensorPullback q).obj E
  let D := (Modules.tensorPullback q).obj (Modules.dual E)
  let ev : MonoidalCategoryStruct.tensorObj M D ⟶ SheafOfModules.unit (pullback f j).ringCatSheaf :=
    (Modules.picardTensorObjIso q E (Modules.dual E)).inv ≫
      (Modules.tensorPullback q).map (Modules.dualEvaluation E) ≫
        (Modules.picardTensorUnitIso q).hom
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
  change IsIso (MonoidalClosed.curry (Modules.picardPushforwardPairing p hO M D ev)) ↔
    IsIso (adj.counit.app M)
  constructor
  · intro h
    have : ((Modules.pushforward p).obj M).IsFiniteLocallyFree := hN
    have : IsSplitMono (adj.counit.app M) :=
      Modules.isSplitMono_counit_of_isIso_picardPushforwardPairing p hO M D ev h
    exact isIso_of_isSplitMono_of_picard_local_ranks f E j
      ((Modules.pushforward p).obj M) hRanks (adj.counit.app M)
  · intro h
    exact Modules.isIso_curry_picardPushforwardPairing_of_isIso_counit p hO M D ev
      (Modules.isIso_curry_picardPullbackEvaluation q E) h

end AlgebraicGeometry.Scheme
