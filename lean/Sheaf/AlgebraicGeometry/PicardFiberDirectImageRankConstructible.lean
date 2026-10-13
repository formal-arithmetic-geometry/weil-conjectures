/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.PerfectJumpLoci

/-! # Constructible ranks of ordinary direct images on fibres

Source: Stacks Project, Tags 0B91(2) and 0BDI(3).
(blueprint: lem-sc-picard-fiber-direct-image-rank-constructible).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The rank-r locus of the ordinary direct image on residue-field fibres is
locally constructible. No rank condition on E along a whole fibre is required.
Source: Stacks Project, Tags 0B91(2) and 0BDI(3), as used in the second proof
paragraph of Tag 0BDP.
(blueprint: lem-sc-picard-fiber-direct-image-rank-constructible).

Proof:
1. E is finitely presented and flat over S: it is finite locally free on X and f
   is flat. Properness and local finite presentation give finite presentation of f.
   Apply perfect direct image and arbitrary base change (Tag 0B91(2)) to E.
2. On Spec kappa(s), its derived fibre has degree-zero cohomology equal to the
   ordinary direct image of E pulled back to X_s. This uses the canonical
   derived-to-ordinary pullback comparison and degree-zero direct-image identification.
3. A quasi-coherent module on the spectrum of a field is finite locally free of
   rank r exactly when its vector space of global sections has dimension r.
   The vector spaces here are finite dimensional by perfectness.
4. Consequently the displayed locus is the degree-zero Betti-number level set of
   Rf_*E. Perfect implies pseudo-coherent, and Tag 0BDI(3) makes this set locally
   constructible. On an empty fibre the vector space is zero, so such points occur
   precisely in the level r=0. -/
theorem picardFiberDirectImageRank_locallyConstructible {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    Topology.IsLocallyConstructible {s : S |
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.pushforward (pullback.snd f (S.fromSpecResidueField s))).obj
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E)) r} := by
  sorry

end AlgebraicGeometry.Scheme
