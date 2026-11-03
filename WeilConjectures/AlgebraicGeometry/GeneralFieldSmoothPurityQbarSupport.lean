/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-- The Q-bar compact-support operation preserves bounded constructibility over a
finite or algebraically closed field. This is the compactification scalar-change
part of the proof of `smoothPurityQbar`; it is strictly weaker than the adjunction.
Source: the compact-support clause of the proof of `sk-thm-sp-qbar`.
Proof plan: choose a finite coefficient model for the input by the Q-bar two-colimit
object clause. Apply the finite-coefficient lower-shriek constructibility theorem to
that model and use scalar-six compact-support comparison for the chosen compactification.
The finite or algebraically closed hypothesis supplies the finite ell-cohomological
dimension bound. Transport the resulting finite-Tor predicate across
`integral_ctf_equals_bc`, and compose the model isomorphism with the Q-bar comparison.
-/
theorem generalFieldQbarSupportClosed
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] (_hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) X.left,
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) Y.left
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj ell)
          (CondensedRing.compactificationOverField f)).obj K.obj) := by
  sorry
end AlgebraicGeometry.ProEtale
