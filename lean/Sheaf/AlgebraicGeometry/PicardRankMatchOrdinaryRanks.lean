/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Ordinary ranks under iterated Picard base change

Source: Stacks Project, Tag 0BDP, first three proof paragraphs.
(blueprint: lem-sc-picard-rank-match-ordinary-ranks).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The ordinary direct image is finite locally free, and its further direct images
have one fixed rank on each sufficiently small base neighbourhood.
Source: Stacks Project, Tag 0BDP, rank decomposition and the ordinary rank dictionary.
(blueprint: lem-sc-picard-rank-match-ordinary-ranks).

Proof:
1. Apply the universal rank test to the identity of T. The canonical isomorphism
   between X times_S T and X times_S (id_T followed by g), and identity tensor
   pullback, identify its first two tests with restrictions of the direct images of
   E and its dual. These local fixed-rank frames give finite local freeness of M.
2. For each s choose this neighbourhood V and rank r. The third test gives rank r
   to E over X_V. Separate V into its intersection with the image of p and its
   complement. The image of p is clopen: p is proper, and flat of finite presentation.
   Keep the part containing s. On the empty-fibre part every further direct image
   is zero, and use rank zero for all further tests.
3. On the nonempty-fibre part, apply the universal rank test after any k:Y to V.
   Around each y it supplies a rank n for the further ordinary direct image and E
   on its inverse image. The fibre above y is nonempty: a nonempty scheme over
   kappa(k(y)) remains nonempty after extension to kappa(y). Choose a fibre point.
   Its local ring is nonzero. Pulling the two frames of E to this point gives free
   modules of ranks r and n, so invariant basis number gives r=n. The dual has the
   same rank, since dualizing a finite free frame preserves its size.
4. Pullback associativity identifies the iterated fibre product with X times_S Y,
   and identifies the iterated tensor pullback of F with its direct pullback.
   Transport the rank tests across these isomorphisms. Fixed-rank finite local
   freeness is local on Y, so the pointwise neighbourhoods give rank r globally on Y.
   This argument includes r=0; on empty Y every fixed-rank condition is vacuous. -/
theorem picardRankMatch_ordinary_ranks {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
    let G := (Modules.tensorPullback (pullback.fst f g)).obj F
    let M := (Modules.pushforward (pullback.snd f g)).obj G
    M.IsFiniteLocallyFree ∧
      ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ r : ℕ,
        ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Modules.pushforward (pullback.snd (pullback.snd f g) (k ≫ U.ι))).obj
              ((Modules.tensorPullback (pullback.fst (pullback.snd f g) (k ≫ U.ι))).obj G))
            r := by sorry

end AlgebraicGeometry.Scheme
