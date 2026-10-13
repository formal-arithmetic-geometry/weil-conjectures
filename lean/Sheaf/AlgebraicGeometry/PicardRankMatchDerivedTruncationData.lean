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

import Sheaf.AlgebraicGeometry.PicardRankMatchOrdinaryRanks
import Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare
import Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Derived truncation data for universally rank-matched Picard direct images

Source: Stacks Project, Tags 0BDP, 0B91(2), and 08HY.
(blueprint: lem-sc-picard-rank-match-derived-truncation-data).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteLocallyFree_isFlatOver {A B : Scheme.{u}} (p : A ⟶ B)
    [Flat p] (G : A.Modules) [G.IsFiniteLocallyFree] : G.IsFlatOver p := by
  intro V U e
  let := (p.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(B, V.1) Γ(A, U.1) :=
    HasRingHomProperty.appLE @Flat p ‹_› V U e
  have : Module.Projective Γ(A, U.1) Γ(G, U.1) :=
    (Modules.finitePresentation_projective_sections G U.2).2
  let : Module Γ(B, V.1) Γ(G, U.1) := Module.compHom _ (p.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(B, V.1) Γ(A, U.1) Γ(G, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(B, V.1) Γ(A, U.1) Γ(G, U.1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
            e0.hom ≫ H.map ((derivedPullback k).map a) := by
  classical
  have inj (Y : Scheme.{u}) : HasInjectiveResolutions Y.Modules :=
    inferInstanceAs (HasInjectiveResolutions
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let G : (pullback f g).Modules := (Modules.tensorPullback (pullback.fst f g)).obj F
  let p := pullback.snd f g
  let M := (Modules.pushforward p).obj G
  let K := (schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj G)
  let a := Modules.canonicalSingleDirectImageMap p G
  have : F.IsFiniteLocallyFree := by
    rcases hF with rfl | rfl
    · infer_instance
    · exact Modules.IsFiniteLocallyFree.dual E
  have : ((Modules.pullback (pullback.fst f g)).obj F).IsFiniteLocallyFree :=
    inferInstance
  let t := (Classical.choose (Modules.exists_tensorPullbackAdjunction
    (pullback.fst f g))).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction (pullback.fst f g))
  have : G.IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} (t.app F).symm
  obtain ⟨hM, hrank⟩ := picardRankMatch_ordinary_ranks f E g hR F hF
  have : M.IsFiniteLocallyFree := hM
  let add : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Modules.tensorPullback k).Additive :=
    fun k ↦ Modules.canonicalTensorPullbackAdditive k
  have hflat : G.IsFlatOver p := finiteLocallyFree_isFlatOver p G
  obtain ⟨hperfect, hbc⟩ := perfect_derivedDirectImage_baseChange p G hflat
  have ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map a) := by
    have hu := Modules.canonicalDirectImageH0Unit p G
    have hi : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map a ≫
        (Modules.canonicalDirectImageH0Iso p G).hom) := by
      change IsIso (_ ≫ (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage p.toLRSHom.toShHom) G 0 ≪≫
          (Modules.pushforward p).rightDerivedZeroIsoSelf.app G).hom)
      rw [hu]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Modules.canonicalDirectImageH0Iso p G).hom
  have comparisons (Y : Scheme.{u}) (k : Y ⟶ T) :=
    Modules.tensorDegreeZeroMateSquare p k G
  have neg (Y : Scheme.{u}) (k : Y ⟶ T) (i : ℤ) (hi : i < 0) :
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedPullback k).obj K)) := by
    obtain ⟨e0, φ, hφ, heq⟩ := comparisons Y k
    have : IsIso φ := hbc k φ hφ
    let N := (Modules.tensorPullback (pullback.fst p k)).obj G
    have hge := (RingedSpace.moduleDirectImage
      (pullback.snd p k).toLRSHom.toShHom).isGE_rightDerivedFunctor_obj_singleFunctor N
    have hz := (DerivedCategory.isGE_iff _ 0).mp hge i hi
    exact hz.of_iso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).mapIso (asIso φ))
  have cmp (Y : Scheme.{u}) (k : Y ⟶ T) :
      let H := DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
      ∃ (e0 : (Modules.tensorPullback k).obj M ≅
          H.obj ((derivedPullback k).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).obj M)))
        (e1 : H.obj ((derivedPullback k).obj K) ≅
          (Modules.pushforward (pullback.snd p k)).obj
            ((Modules.tensorPullback (pullback.fst p k)).obj G)),
        Modules.moduleBaseChangeMap p (pullback.snd p k) k
            (pullback.fst p k) pullback.condition G ≫ e1.inv =
          e0.hom ≫ H.map ((derivedPullback k).map a) := by
    obtain ⟨e0, φ, hφ, heq⟩ := comparisons Y k
    have : IsIso φ := hbc k φ hφ
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let e1 := H.mapIso (asIso φ) ≪≫
      Modules.canonicalDirectImageH0Iso (pullback.snd p k)
        ((Modules.tensorPullback (pullback.fst p k)).obj G)
    have he : Modules.moduleBaseChangeMap p (pullback.snd p k) k
        (pullback.fst p k) pullback.condition G ≫ e1.inv =
        e0.hom ≫ H.map ((derivedPullback k).map a) := by
      apply (Iso.comp_inv_eq e1).2
      simpa only [e1, H, a, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
        Category.assoc] using heq
    exact ⟨e0, e1, he⟩
  refine ⟨K, a, hperfect, neg, ?_, ha, cmp⟩
  intro s
  obtain ⟨U, hs, r, hr⟩ := hrank s
  refine ⟨U, hs, r, ?_⟩
  intro Y k
  obtain ⟨e0, e1, he⟩ := cmp Y (k ≫ U.ι)
  have := hr Y k
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e1.symm

end AlgebraicGeometry.Scheme
