module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The source and target stalks are finite free, without comparing their ranks.
Source: Stacks Project, Tags 01C6 and 0098; the local frames in the rank reduction
of Tag 0BDP. This is the finite-freeness part of the original stalk-rank argument.

Proof: apply hR to the identity of T at h(t). Use the identity law on morphisms
and choose a trivializing open inside the resulting neighbourhood for the direct
image of E, or for that of its dual according to hF. Taking germs of the frame
and its coordinate projections gives a finite basis at h(t). The pullback stalk
formula identifies P_t with extension of scalars of this module along h's stalk
map; tensoring its basis gives a finite basis of P_t.
For Q, apply hR to h at t. The associativity isomorphism between the iterated
fibre product and X times_S T', together with composition of tensor pullbacks,
identifies the iterated pulled-back F with the pullback of F along the composite
base change. Pushforward along this isomorphism identifies Q with the direct
image occurring in hR. Choose a trivializing open inside the resulting
neighbourhood and take germs of its frame to obtain a finite basis of Q_t.
The two bases can have unrelated cardinalities at this stage. No proper-image
or fibre-rank comparison is needed. A zero-rank frame gives an empty basis;
there is no point t when T' is empty.
(blueprint: lem-sc-picard-base-change-stalk-finite-bases) -/
theorem picardRankMatch_baseChange_stalk_finite_bases {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) (t : T') :
    let P := (Modules.tensorPullback h).obj
      ((Modules.pushforward (pullback.snd f g)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    let Q := (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
      ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    (∃ r : ℕ, Nonempty (Module.Basis (Fin r) (T'.presheaf.stalk t)
      (P.presheaf.stalk t))) ∧
    (∃ s : ℕ, Nonempty (Module.Basis (Fin s) (T'.presheaf.stalk t)
      (Q.presheaf.stalk t))) := by
  sorry

end AlgebraicGeometry.Scheme
