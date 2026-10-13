/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Derived truncation data for universally rank-matched Picard direct images

Source: Stacks Project, Tags 0BDP, 0B91(2), and 08HY.
(blueprint: lem-sc-picard-rank-match-derived-truncation-data).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A universally rank-matched Picard direct image has connective perfect derived
truncation data, with the ordinary canonical comparison identified in degree zero.
This supplies the geometric dictionary, without asserting that any comparison map
is surjective or invertible.
Source: Stacks Project, Tag 0BDP, second and third proof paragraphs; Tag 0B91(2);
Tag 08HY, canonical comparison and its adjoint description.
(blueprint: lem-sc-picard-rank-match-derived-truncation-data).

Proof:
1. Put p = pr2 : X times_S T to T and G = pr1* F, and take K = Rp_*(G[0]).
   Finite locally free modules and their duals remain finite locally free under
   tensor pullback. Since p is proper, flat and finitely presented, G is finitely
   presented and relatively flat. Tag 0B91(2) makes K perfect and identifies its
   derived pullback along every k with the derived direct image of the further
   pulled-back module. Nonnegative injective resolutions show negative cohomology
   vanishes for every such pullback.
2. At s choose the common-rank open given by hR for the identity of T. Tensor
   pullback along the identity identifies its three rank tests with the displayed
   modules. On the nonempty-fibre locus, rank of G is the chosen r, and it stays r
   under every further base change. The corresponding tests of hR therefore give
   rank r to H0(Lk*K), using the canonical derived-direct-image comparison.
   The empty-fibre locus is open by properness; there the direct image is zero and
   choose r = 0. Flatness and finite presentation make the nonempty-fibre locus
   open as well. Shrink the original open into the appropriate locus. Finite local
   freeness of rank r is local on the base, so these tests supply the universal
   assertion over the whole open. Associativity of pullbacks identifies iterated
   fibre products with the tests in hR. For F dual E, tensor pullback preserves
   duality and its rank is the same as E.
3. The identity test also makes M = p_*G finite locally free. The standard degree
   zero direct-image identification H0(K) = M and connective truncation give a:
   M[0] to K whose H0 map is an isomorphism. Flatness of M identifies Lk*(M[0])
   with (k*M)[0], supplying e0; derived base change and the same degree-zero
   direct-image identification supply e1. They exist without matrix vanishing.
4. Compute the transpose of the derived comparison with the canonical adjunction
   pinned to its underived unit. Naturality of the resolution augmentation and
   the adjunction triangle identities identify its H0 map with pushforward of
   the pullback unit, then pushforward composition, square commutation and inverse
   composition. This is exactly moduleBaseChangeMap, rather than an arbitrary
   map between the isomorphic objects. Naturality of connective truncation gives
   beta followed by e1.inv = e0.hom followed by H0(Lk*a). The pullback composition
   comparisons account for the iterated fibre product in the target. These
   equalities agree on open overlaps, so glue globally. No matrix-zero calculation
   or invertibility of beta is used in this construction. -/
theorem picardRankMatch_derived_truncation_data
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
    let M := (Modules.pushforward (pullback.snd f g)).obj
      ((Modules.tensorPullback (pullback.fst f g)).obj F)
    ∃ (K : schemeDerivedCategory T)
      (a : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M ⟶ K),
      IsPerfect T K ∧
      (∀ (Y : Scheme.{u}) (k : Y ⟶ T) (i : ℤ), i < 0 →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
            ((derivedPullback k).obj K))) ∧
      (∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ r : ℕ,
        ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((derivedPullback (k ≫ U.ι)).obj K)) r) ∧
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map a) ∧
      ∀ (Y : Scheme.{u}) (k : Y ⟶ T),
        let H := DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
        ∃ (e0 : (Modules.tensorPullback k).obj M ≅
            H.obj ((derivedPullback k).obj ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M)))
          (e1 : H.obj ((derivedPullback k).obj K) ≅
            (Modules.pushforward (pullback.snd (pullback.snd f g) k)).obj
              ((Modules.tensorPullback (pullback.fst (pullback.snd f g) k)).obj
                ((Modules.tensorPullback (pullback.fst f g)).obj F))),
          Modules.moduleBaseChangeMap (pullback.snd f g)
              (pullback.snd (pullback.snd f g) k) k
              (pullback.fst (pullback.snd f g) k) pullback.condition
              ((Modules.tensorPullback (pullback.fst f g)).obj F) ≫ e1.inv =
            e0.hom ≫ H.map ((derivedPullback k).map a) := by sorry

end AlgebraicGeometry.Scheme
