/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.SixFunctors.ProperImageLocalizingProper
import Sheaf.Paper.ContinuousAlgClLocalFree
import Sheaf.Paper.ProperHeartConstructibleCohomology
import WeilConjectures.RepresentationTheory.IntegralModel

/-!
# Proper direct image for the continuous-map algebraic-closure coefficient

Source: blueprint main-20261015, det-sf-comp-coherence-single, proper-image paragraph.
(blueprint: det-sf-comp-continuous-algcl-heart-finiteness).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Higher proper direct images of one constructible sheaf have constructible cohomology
for the full continuous-map algebraic-closure coefficient.

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change, assertion (1),
in degree zero, as used in det-sf-comp-coherence-single's proper-image paragraph.
(blueprint: det-sf-comp-continuous-algcl-heart-finiteness).

Proof: choose a finite adapted stratification and its finite extension-by-zero
filtration, refining the strata to normal strata. Finite constant presentations are
locally finite free over the algebraic-closure field. The monodromy of each lisse
piece on a normal stratum is profinite. The proved source-library theorem
PadicAlgCl.exists_finiteDimensional_forall_mem gives a finite coefficient field.
For each stratum, descend the finite-rank monodromy to this finite field and extend
it by zero. Apply properHeart_constructible_cohomology for that finite coefficient;
its integral-lattice and torsion arguments are already in the library. The integral
finiteness and uniform bound give a bounded finite-projective cochain model on an
adapted target stratum. Compute the canonical coefficient comparison on these finite
terms: finite sums, differentials and their actions commute with coefficient change.
Invert ell and extend the finite model to the actual full continuous coefficient.
The finite sheaf
filtration and the long exact cohomology sequence give constructibility for the
original sheaf. Empty strata and the zero sheaf contribute zero. This result asks
only for constructibility; negative cohomology vanishes by left t-exactness. Bounds,
finite Tor amplitude and bounded-complex devissage
are separate. Every scalar comparison here concerns the actual continuous-map ring;
it is not replaced by the finite-subextension-valued colimit coefficient. -/
theorem continuousAlgCl_proper_heart_finiteness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : ConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) X) :
    ∀ n : ℤ, IsConstantModelConstructible
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) Y
      ((DerivedCategory.homologyFunctor _ n).obj
        ((lowerStar (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
