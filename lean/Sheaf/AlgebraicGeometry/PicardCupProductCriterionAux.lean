module

public import Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The dual direct image is finite locally free under the universal rank condition.
Source: Stacks Project, Tag 0BDP, rank decomposition and local dual-basis argument.
(blueprint: new-picard-dual-direct-image-finite-locally-free)

Proof: Apply the universal rank condition after every base change.  On each open
neighbourhood supplied by that condition, the direct image of the dual has a
finite free presentation of the indicated rank.  These local presentations glue
by uniqueness of finite locally free structures, giving the asserted global
finite locally free module. -/
theorem picard_dual_directImage_isFiniteLocallyFree {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree]
    {W : Scheme.{u}} (j : W ⟶ S)
    (hW : ∀ {T : Scheme.{u}} (h : T ⟶ W), PicardDirectImageRankCondition f E (h ≫ j)) :
    ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))).IsFiniteLocallyFree := by
  classical
  have _hO := hO j
  let N := (Modules.pushforward (pullback.snd f j)).obj
    ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))
  have hlocal (w : W) : ∃ U : W.Opens, w ∈ U ∧
      ((Modules.tensorPullback U.ι).obj N).IsFiniteLocallyFree := by
    obtain ⟨U, hw, r, _, hN, _⟩ := (hW (𝟙 W)).2.1 (𝟙 W) w
    have hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj N) r := by
      exact (congrArg (fun k : W ⟶ S ↦
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback U.ι).obj
            ((Modules.pushforward (pullback.snd f k)).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj (Modules.dual E)))) r)
        (by simp : 𝟙 W ≫ 𝟙 W ≫ j = j)).mp hN
    have := hr
    exact ⟨U, hw, SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} _ r⟩
  choose U hw hU using hlocal
  apply Modules.isFiniteLocallyFree_of_isOpenImmersion N (fun w ↦ (U w).ι)
  · apply eq_top_iff.mpr
    intro w _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, by
      rw [Scheme.Opens.opensRange_ι]
      exact hw w⟩
  · intro w
    have := hU w
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
      (((Classical.choose (Modules.exists_tensorPullbackAdjunction (U w).ι)).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (U w).ι)).app N)

/-- Once both direct images are finite locally free, cup product detects the
adjunction counit after arbitrary base change.
Source: Stacks Project, Tag 0BDP, final two proof paragraphs.
(blueprint: new-picard-cup-product-equivalence)

Proof: Push evaluation forward and compose with the inverse of the structure
sheaf unit to obtain the cup pairing, then transpose it.  Finite free dual bases
show that an invertible transpose gives a left inverse to the evaluation counit;
equal ranks make this a two-sided inverse.  Conversely an invertible counit
identifies the bundle with a pullback of its pushforward, and dualizing plus the
finite free projection formula identifies the pairing with ordinary evaluation. -/
theorem picard_cupProductCriterion_of_finiteLocallyFree
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree]
    {W : Scheme.{u}} (j : W ⟶ S)
    (hW : ∀ {T : Scheme.{u}} (h : T ⟶ W), PicardDirectImageRankCondition f E (h ≫ j))
    (hD : ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))).IsFiniteLocallyFree) :
    ∃ φ : ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))) ⟶
      Modules.dual ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj E)),
      ∀ {T : Scheme.{u}} (h : T ⟶ W),
        IsIso ((Modules.tensorPullback h).map φ) ↔
          IsIso ((Classical.choose
            (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).counit.app
              ((Modules.tensorPullback (pullback.fst f (h ≫ j))).obj E)) := by
  sorry

end AlgebraicGeometry.Scheme
