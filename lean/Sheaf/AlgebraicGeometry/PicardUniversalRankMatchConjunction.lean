/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-! # Synchronizing the two local rank conditions

Source: Stacks Project, Tag 0BDP, rank decomposition and the two rank-r loci.
(blueprint: lem-sc-picard-universal-rank-match-conjunction).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorIso {A B : Scheme.{u}} (a : A ⟶ B) :
    Modules.tensorPullback a ≅ Modules.pullback a :=
  (Classical.choice (Modules.nonempty_tensorPullbackAdjunction a)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)

private theorem tensorRank {A B : Scheme.{u}} (a : A ⟶ B) (M : B.Modules) (r : ℕ)
    (hr : M.IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback a).obj M).IsFiniteLocallyFreeOfRank r := by
  let := hr
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ((tensorIso a).app M).symm

private theorem tensorRankComp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) (r : ℕ)
    (hr : ((Modules.tensorPullback b).obj M).IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback (a ≫ b)).obj M).IsFiniteLocallyFreeOfRank r := by
  have hr' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback b ⋙ Modules.tensorPullback a).obj M) r := tensorRank a _ r hr
  let := hr'
  obtain ⟨e⟩ := Modules.nonempty_tensorPullbackComp a b
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e.app M).symm

private theorem rankOnSmallerOpen {A : Scheme.{u}} (M : A.Modules)
    {U W : A.Opens} (hWU : W ≤ U) (r : ℕ)
    (hr : ((Modules.tensorPullback U.ι).obj M).IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback W.ι).obj M).IsFiniteLocallyFreeOfRank r := by
  simpa only [Scheme.homOfLE_ι] using tensorRankComp (A.homOfLE hWU) U.ι M r hr

private theorem referenceRankOnSmallerOpen {X S A : Scheme.{u}}
    (f : X ⟶ S) (k : A ⟶ S) (E : X.Modules) {U W : A.Opens}
    (hWU : W ≤ U) (r : ℕ)
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ k))).obj E) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (W.ι ≫ k))).obj E) r := by
  let i := A.homOfLE hWU
  let q : pullback f (W.ι ≫ k) ⟶ pullback f (U.ι ≫ k) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i) (by
      change pullback.fst f (W.ι ≫ k) ≫ f =
        pullback.snd f (W.ι ≫ k) ≫ (i ≫ U.ι ≫ k)
      rw [← Category.assoc i U.ι k]
      dsimp only [i]
      rw [Scheme.homOfLE_ι]
      exact pullback.condition)
  have hq : q ≫ pullback.fst f (U.ι ≫ k) = pullback.fst f (W.ι ≫ k) := by
    simp [q]
  simpa only [hq] using tensorRankComp q (pullback.fst f (U.ι ≫ k)) E r hr

private theorem nonempty_of_unit_iso {A B : Scheme.{u}} (a : A ⟶ B)
    [Nonempty B]
    (ha : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).unit.app
      (SheafOfModules.unit B.ringCatSheaf))) : Nonempty A := by
  classical
  by_contra h
  have : IsEmpty A := not_nonempty_iff.mp h
  let := ha
  have hz := Modules.isZero_of_isEmpty
    ((Modules.tensorPullback a).obj (SheafOfModules.unit B.ringCatSheaf))
  exact Modules.not_isZero_unit B
    (((Modules.pushforward a).map_isZero hz).of_iso
      (asIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).unit.app
        (SheafOfModules.unit B.ringCatSheaf))))

/-- The two single-image conditions give the common-neighbourhood condition.
Source: Stacks Project, Tag 0BDP, first and third proof paragraphs: both loci
use the rank fixed by E, not independent ranks inferred from the direct images.
(blueprint: lem-sc-picard-universal-rank-match-conjunction).

Proof: Fix a further base change h and a point t. Choose neighbourhoods U
and V and witness ranks r and s for the two single-image conditions. Set W=U∩V;
it contains t. Restriction by the inclusions W→U and W→V preserves finite local
freeness of fixed rank. The composition isomorphisms for tensor pullback, and
canonical maps between the corresponding fibre products, identify the two
restrictions of E with its pullback to X_W. The intersection W is nonempty because
it contains t. The structure-sheaf unit hypothesis at W implies that X_W is
nonempty: otherwise every module on X_W is zero, and its direct image is zero,
contradicting the nonzero structure module on W. Choose a point of X_W; the
stalk of the reference pullback of E has both ranks r and s. Scheme local
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
    PicardUniversalRankMatch f E g := by
  intro T' h t
  obtain ⟨U, htU, r, hUr, hEr⟩ := hE h t
  obtain ⟨V, htV, s, hVs, hEs⟩ := hdual h t
  let W := U ⊓ V
  have htW : t ∈ W := ⟨htU, htV⟩
  have hPr := rankOnSmallerOpen _ (show W ≤ U from inf_le_left) r hUr
  have hQs := rankOnSmallerOpen _ (show W ≤ V from inf_le_right) s hVs
  have hWr := referenceRankOnSmallerOpen f (h ≫ g) E
    (show W ≤ U from inf_le_left) r hEr
  have hWs := referenceRankOnSmallerOpen f (h ≫ g) E
    (show W ≤ V from inf_le_right) s hEs
  have : Nonempty (W : Scheme) := ⟨⟨t, htW⟩⟩
  have hn := nonempty_of_unit_iso (pullback.snd f (W.ι ≫ h ≫ g))
    (hO (W.ι ≫ h ≫ g))
  obtain ⟨x⟩ := hn
  have hrs : r = s := by
    have hr := @Modules.finiteLocallyFreeOfRank_stalk_finrank _ _ r hWr x
    have hs := @Modules.finiteLocallyFreeOfRank_stalk_finrank _ _ s hWs x
    exact hr.symm.trans hs
  subst s
  exact ⟨W, htW, r, hPr, hQs, hWr⟩

end AlgebraicGeometry.Scheme
