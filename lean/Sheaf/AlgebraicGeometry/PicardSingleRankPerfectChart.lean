/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Perfect charts for one direct-image rank condition

Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-perfect-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

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
   flatness, since f is flat. Apply perfect_derivedDirectImage_baseChange to F.
   Restrict the resulting perfect complex to a neighbourhood with finite Tor bound b.
   Arbitrary derived base change has no negative cohomology, so the bound starts at zero.
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
                  ((derivedPullback (h ≫ g)).obj K)) r := by sorry

end AlgebraicGeometry.Scheme
