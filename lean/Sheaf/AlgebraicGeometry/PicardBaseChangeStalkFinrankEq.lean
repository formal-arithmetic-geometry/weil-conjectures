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

/-- The source and target stalks have equal finrank, without asserting freeness.
Source: Stacks Project, Tag 0BDP, local rank reduction, expanded using
Tags 01C6 and 0098. This is the rank-comparison part of the original argument.

Proof: apply hR to the identity at h(t), obtaining a neighbourhood V and rank r,
and to h at t, obtaining W and rank s. Local frames, the pullback stalk formula,
and associativity of fibre products identify the finrank of P_t with r and that
of Q_t with s. To compare r and s, first suppose the fibre over h(t) is nonempty.
For a point x in that fibre, the tensor product of kappa(x) and kappa(t) over
kappa(h(t)) is nonzero (fields are faithfully flat). Choose a prime of this
tensor product to obtain a point y of the iterated fibre product over x and t.
At y the pulled-back E has rank r from V and rank s from W. The stalk formula
transports the frames to this same local ring. Invariant basis number over the
nonzero scheme local ring gives r = s. Thus the two computed finranks coincide.
If the fibre is empty, the proper projection X times_S T to T has closed image
omitting h(t). On its open complement the direct image of either F is zero.
Its pullback along h is zero, and the base-changed projection also has empty
inverse image over the inverse-image open. Hence both stalks are zero and
both finranks are zero, regardless of the r and s selected by hR on empty
preimages. This handles rank zero as well; empty T' has no point to check.
(blueprint: lem-sc-picard-base-change-stalk-finrank-eq) -/
theorem picardRankMatch_baseChange_stalk_finrank_eq {X S T : Scheme.{u}} (f : X ⟶ S)
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
    Module.finrank (T'.presheaf.stalk t) (P.presheaf.stalk t) =
      Module.finrank (T'.presheaf.stalk t) (Q.presheaf.stalk t) := by
  sorry

end AlgebraicGeometry.Scheme
