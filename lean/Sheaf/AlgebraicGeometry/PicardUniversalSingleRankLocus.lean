/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.LocalImmersionLocus
import Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart
import Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal
import Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus

/-! # The locus for one direct-image rank condition

Source: Stacks Project, Tags 0BDP and 0BDL.
(blueprint: lem-sc-picard-universal-single-rank-locus).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Represent just one direct-image rank condition, with E as the reference bundle.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs, applying Tag 0BDL
to one perfect direct image at a time.
(blueprint: lem-sc-picard-universal-single-rank-locus).

Proof:
1. The universal structure-sheaf unit makes every geometric fibre nonempty and
   connected: its ring of global functions is the residue field, so it has no
   nontrivial idempotents. The locally constant rank of E is constant on each fibre.
   Since f is open and closed, the images of its clopen rank loci are disjoint
   clopen subsets covering S. Let S_r be the image of the rank-r locus of E.
2. On each S_r, E and all its further pullbacks have constant rank r. The finite
   locally free F is finitely presented and flat over S_r. Proper flat cohomology
   and base change (Tag 0B91(2)) identify the ordinary direct image after any base
   change with H^0 of the derived pullback of the perfect complex Rf_*F. There is
   no negative cohomology after any base change. Locally choose a finite Tor bound b.
3. Apply the lowest-cohomology locus theorem (Tag 0BDL) with a=0 and this fixed r.
   The resulting immersion represents universal rank-r freeness of this single
   direct image. In the stated local condition, the reference E forces every
   local witness rank to equal r: restrict to any nonempty fibre and compute its
   stalk rank. Finite local freeness of rank r is local on the test scheme, so
   these local witnesses are equivalent to the universal rank-r condition.
4. The constructions for different finite Tor-bound neighbourhoods agree by their
   universal property. Immersions are monomorphisms, so their unique identifications
   satisfy the cocycle condition and glue. Glue also across the disjoint clopen S_r.
   The resulting morphism is an immersion because this property is local on S.
   A test morphism factors locally exactly when the displayed condition holds;
   uniqueness through a monomorphism glues the local factors. Empty test schemes
   require no witnesses at points, and rank zero uses the same construction. -/
theorem exists_picardUniversalSingleRankLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (E F : X.Modules) [E.IsFiniteLocallyFree] [F.IsFiniteLocallyFree] :
    ∃ (W : Scheme.{u}) (j : W ⟶ S),
      IsImmersion j ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S),
        (∃ h : T ⟶ W, h ≫ j = g) ↔ PicardUniversalSingleRankMatch f E F g := by
  let : ∀ T : Scheme.{u}, HasDerivedCategory
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) :=
    fun T ↦ HasDerivedCategory.standard _
  let : ∀ (T : Scheme.{u}) (U : T.Opens), HasDerivedCategory
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U)) :=
    fun T U ↦ HasDerivedCategory.standard _
  apply exists_localImmersionLocus S (fun g ↦ PicardUniversalSingleRankMatch f E F g)
  · intro T T' g h hg T'' k t
    convert hg (k ≫ h) t using 1
    congr! 8
  · intro T g hlocal
    exact picardUniversalSingleRankMatch_of_source_local f E F g hlocal
  · intro s
    obtain ⟨U, hs, K, b, r, hK, hamp, hmatch⟩ :=
      exists_picardSingleRankPerfectChart f hO E F s
    obtain ⟨W, j, hj, _, _, hfactor, _, _⟩ :=
      exists_perfectLowestCohomologyLocus U.toScheme K hK 0 b hamp r
    refine ⟨U, hs, W, j, hj, ?_⟩
    intro T g
    exact (hfactor T g).trans (hmatch T g).symm

end AlgebraicGeometry.Scheme
