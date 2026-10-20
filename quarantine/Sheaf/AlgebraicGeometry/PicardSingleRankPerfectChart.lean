/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.PicardReferenceRankNeighbourhood
import Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.PicardFiberRankClopen

/-! # Perfect charts for one direct-image rank condition

Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-perfect-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Tensor pullback along an open inclusion agrees with ordinary restriction. -/
private noncomputable def tensorOpenIso {T : Scheme.{u}} (M : T.Modules) (U : T.Opens) :
    ((Modules.tensorPullback U.ι).obj M) ≅ M.restrict U.ι :=
  ((Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction U.ι)).app M ≪≫
      ((Modules.restrictFunctorIsoPullback U.ι).app M).symm

/-- On a surjective fixed-rank stratum, the local witnesses have exactly that rank. -/
private theorem singleRankMatch_iff_of_fixedRank {X S T : Scheme.{u}}
    (f : X ⟶ S) [Surjective f] (E F : X.Modules) (U : S.Opens) (r : ℕ)
    (hE : ∀ (Y : Scheme.{u}) (a : Y ⟶ U.toScheme),
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (a ≫ U.ι))).obj E) r)
    (g : T ⟶ U.toScheme) :
    PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
      ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F)) r := by
  classical
  constructor
  · intro hmatch T' h
    let M := (Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
      ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F)
    have hlocal (t : T') : ∃ W : T'.Opens, t ∈ W ∧
        (M.restrict W.ι).IsFiniteLocallyFreeOfRank r := by
      obtain ⟨W, ht, n, hM, hN⟩ := hmatch h t
      have hr := hE W.toScheme (W.ι ≫ h ≫ g)
      rw [Category.assoc] at hr
      let N := (Modules.tensorPullback
        (pullback.fst f (W.ι ≫ h ≫ g ≫ U.ι))).obj E
      have hn : N.IsFiniteLocallyFreeOfRank n := by simpa only [Category.assoc] using hN
      have hr' : N.IsFiniteLocallyFreeOfRank r := hr
      obtain ⟨x, _⟩ := (pullback.snd f (W.ι ≫ h ≫ g ≫ U.ι)).surjective
        (⟨t, ht⟩ : W.toScheme)
      have heq : n = r := by
        have := hn
        have hn' := Modules.finiteLocallyFreeOfRank_stalk_finrank N n x
        have := hr'
        have hr'' := Modules.finiteLocallyFreeOfRank_stalk_finrank N r x
        exact hn'.symm.trans hr''
      subst n
      have hM' : ((Modules.tensorPullback W.ι).obj M).IsFiniteLocallyFreeOfRank r := by
        simpa only [Category.assoc] using hM
      have := hM'
      exact ⟨W, ht, SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (tensorOpenIso M W)⟩
    choose W ht hW using hlocal
    apply Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top M W
    · apply eq_top_iff.mpr
      intro t _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, ht t⟩
    · exact hW
  · intro hglobal T' h t
    let M := (Modules.pushforward (pullback.snd f (h ≫ g ≫ U.ι))).obj
      ((Modules.tensorPullback (pullback.fst f (h ≫ g ≫ U.ι))).obj F)
    have : M.IsFiniteLocallyFreeOfRank r := hglobal T' h
    refine ⟨⊤, trivial, r, ?_, ?_⟩
    · have hr : (M.restrict (⊤ : T'.Opens).ι).IsFiniteLocallyFreeOfRank r :=
        inferInstance
      have := hr
      simpa only [Category.assoc] using
        (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
          (tensorOpenIso M (⊤ : T'.Opens)).symm)
    · have hr := hE (⊤ : T'.Opens).toScheme ((⊤ : T'.Opens).ι ≫ h ≫ g)
      rw [Category.assoc] at hr
      exact hr

/-- Near every base point the single-rank predicate is universal rank-r lowest cohomology.
This supplies the input complex and comparison, but constructs no representing locus.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-perfect-chart).

Proof:
1. Apply the structure-sheaf unit on residue-field base changes. Each fibre has
   global functions equal to its residue field, so it is nonempty and connected.
   The rank of E is constant on each fibre. Its constant-fibre-rank locus is clopen
   by picardFiberRank_clopen. Restrict to the stratum through the given point.
   Pullback preserves rank, so every further pullback of E has this fixed rank r.
2. On this stratum, finite local freeness of F gives finite presentation and relative
   flatness, since f is flat. Take a bounded nonnegative flat affine Cech model of
   its direct image on a neighbourhood. Its derived object is perfect. Bounded
   flatness gives K-flatness; tensoring with any module has zero terms outside [0,b].
3. Derived base change and H^0 of the right derived direct image identify H^0 of
   every derived pullback with the ordinary direct image of the pullback of F.
   For a local witness in the single-rank predicate, the rank of the reference E
   equals r: restrict to a nonempty fibre and then its residue-field stalk.
   Fixed-rank finite local freeness is local on the test scheme, so the local
   direct-image witnesses are equivalent to global rank-r freeness on every
   further test scheme. Conversely, global rank-r freeness gives local witnesses
   with r and the already rank-r reference E. Empty test schemes have vacuous
   local conditions and their module sheaves are free of every rank; r=0 needs
   no separate argument. -/
theorem exists_picardSingleRankPerfectChart
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ (T : Scheme.{u}) (U : T.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ (K : schemeDerivedCategory U.toScheme) (b : ℤ) (r : ℕ),
      IsPerfect U.toScheme K ∧
      (∀ M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
        ∀ i : ℤ, i < 0 ∨ b < i →
          schemeDerivedTensorCohomologyVanishes U.toScheme K M i) ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme),
        PicardUniversalSingleRankMatch f E F (g ≫ U.ι) ↔
          ∀ (T' : Scheme.{u}) (h : T' ⟶ T),
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) 0).obj
                  ((derivedPullback (h ≫ g)).obj K)) r := by
  obtain ⟨hsurj, U, hsU, r, hE⟩ := exists_picardReferenceRankNeighbourhood f hO E s
  have : Surjective f := hsurj
  obtain ⟨V, hsV, hVU, K, b, hK, hb, hcomp⟩ :=
    exists_properFlatDirectImagePerfectChart f F U s hsU
  refine ⟨V, hsV, K, b, r, hK, hb, ?_⟩
  intro T g
  have hE' (Y : Scheme.{u}) (a : Y ⟶ V.toScheme) :
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (a ≫ V.ι))).obj E) r := by
    have hr := hE Y (a ≫ S.homOfLE hVU)
    rw [Category.assoc, homOfLE_ι] at hr
    exact hr
  rw [singleRankMatch_iff_of_fixedRank f E F V r hE' g]
  constructor
  · intro hglobal T' h
    obtain ⟨e⟩ := hcomp T' (h ≫ g)
    rw [Category.assoc] at e
    have hr := hglobal T' h
    have := hr
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
  · intro hglobal T' h
    obtain ⟨e⟩ := hcomp T' (h ≫ g)
    rw [Category.assoc] at e
    have hr := hglobal T' h
    have := hr
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e

end AlgebraicGeometry.Scheme
