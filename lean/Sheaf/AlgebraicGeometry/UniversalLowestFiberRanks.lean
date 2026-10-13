/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.PerfectJumpLoci
import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion

/-! # Residue ranks on a universally free lowest locus
Source: Stacks Project, Tags 0BDL, 0BDI, 08E9 and 09U8.
(blueprint: lem-sc-universal-lowest-fiber-ranks). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Tor amplitude and the residue-field rank tests determine the bottom fibre ranks.
Source: Stacks Project, Tag 0BDL, first paragraph of the proof; Tag 0BDI,
fibre base-change formula; Tags 08E9 and 09U8, restriction of Tor amplitude.
(blueprint: lem-sc-universal-lowest-fiber-ranks).

Proof: Set b' = max a b, so a<=b' and the assumed vanishing also gives
Tor amplitude in [a,b']. Restrict to an affine neighbourhood of h(t).
To test against a module G on this open, extend it to S by open pushforward;
its restriction is G. Exact open restriction commutes with tensor and
homology, hence transports the global vanishing tests to the open. A perfect
complex there has a bounded projective module representative. The affine
Tor-amplitude criterion puts that representative in amplitude [a,b'].
Tensor with kappa(h(t)); its cohomology is zero below a. The affine derived
pullback computation identifies this with the derived residue fibre, giving
zero Betti numbers below a. Alternatively use the flat representative in
[a,b'] and termwise pullback, as in Tag 09U8.
For the bottom rank, derived composition identifies the residue test at t
with the residue fibre of Lh*E. A rank-r locally free sheaf on the spectrum
of kappa(t) is free: its trivializing cover has a nonempty member, and every
nonempty open of this one-point spectrum is the whole spectrum. Its global
sections therefore have dimension r. Apply the base-change clause of the
jump-loci theorem to E, which is pseudo-coherent since it is perfect, and h.
It identifies this dimension with the Betti number of E at h(t), giving r.
Rank zero and b<a cause no issue because only the lower bound is needed.
The empty T has no points, so both assertions are vacuous. -/
theorem universalLowest_fiber_ranks
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ) (T : Scheme.{u}) (h : T ⟶ S)
    (hres : ∀ t : T,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (T.residueField t)).toRingedSpace)) a).obj
            ((derivedPullback (T.fromSpecResidueField t ≫ h)).obj E)) r) :
    ∀ t : T, (∀ i : ℤ, i < a → derivedFiberBetti S E i (h t) = 0) ∧
      derivedFiberBetti S E a (h t) = r := by sorry

end AlgebraicGeometry.Scheme
