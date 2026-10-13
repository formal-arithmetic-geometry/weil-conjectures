/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Perfect charts for one direct-image rank condition

Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-unrestricted-perfect-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Near every base point the single-rank predicate is universal rank-r lowest cohomology.
This supplies the input complex and comparison, but constructs no representing locus.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs; Tag 0B91(2).
(blueprint: lem-sc-picard-single-rank-unrestricted-perfect-chart).

Proof:
1. The clopen rank loci X_r of E have open and closed images: flat local finite
   presentation makes f open, and properness makes f closed. The image V=f(X)
   is clopen. For a nonempty homogeneous fibre of rank r, the clopen neighbourhood
   V minus f(X minus X_r) contains only nonempty fibres of this rank.
2. On this neighbourhood finite local freeness makes F finitely presented and
   relatively flat. Tag 0B91 gives perfect Rf_*F and arbitrary derived base change.
   Its pullbacks have no negative cohomology. Shrink near s to a finite strictly
   perfect model of Tor amplitude [0,b]. Degree-zero derived base change identifies
   all its pulled-back H^0 sheaves with the ordinary direct images in the predicate.
   The reference E has rank r on all inverse images. In any local witness its rank
   equals r by invariant basis number on a stalk of a nonempty fibre. Locality of
   rank-r freeness proves the equivalence in both directions, including nonreduced
   tests and rank zero.
3. If s has empty fibre, take U=S minus V. All pullback fibres and direct images
   are empty and zero respectively. The reference clause is vacuous. Take the
   actual zero derived object K, b=0 and r=0: both sides hold on every test scheme.
4. If the fibre at s has two different ranks a and c, take the intersection of the
   images of X_a and X_c as U. Every fibre over U contains both ranks. They persist
   after residue-field extension, so a nonempty test scheme cannot satisfy the
   reference clause, tested at one of its residue-field points. Thus the predicate
   holds exactly for empty tests. Take the actual zero derived object K, b=0 and
   r=1: its pulled-back H^0 is zero, which is rank one exactly on an empty scheme,
   since the residue field at any point of a nonempty scheme is nonzero.
5. These three cases exhaust all fibres. The zero objects in the last two cases
   are perfect and have the stated vanishing. No complex is chosen from an
   undetermined existence claim. Empty tests have vacuous covers, so their module
   sheaves have every finite rank and both equivalences include them. -/
theorem exists_picardSingleRankUnrestrictedPerfectChart
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ (T : Scheme.{u}) (U : T.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
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
