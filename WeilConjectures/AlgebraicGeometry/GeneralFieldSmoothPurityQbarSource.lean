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
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-- The Q-bar twisted pullback preserves bounded constructibility over a finite or
algebraically closed field. This is the Tate-line and shift scalar-change part
of the proof of `smoothPurityQbar`; it is strictly weaker than the adjunction.
Source: the twisted-pullback clause of the proof of `sk-thm-sp-qbar`.
Proof plan: descend the input to a finite subextension, apply the finite-stage
pullback constructibility result, and use the scalar-six pullback comparison.
The coefficient-independent compatible roots identify the finite Tate line after
extension with the prescribed Q-bar line. Ordinary derived tensor associativity and
the shift comparison transport finite Tor amplitude and bounded constructibility;
`integral_ctf_equals_bc` then yields the required constant-model predicate.
-/
theorem generalFieldQbarSourceClosed
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)] (_hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    ∀ K : ConstantModelBoundedConstructible
        (Profinite.padicAlgClRingObj ell) Y.left,
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) X.left
        (((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f.left).mapDerivedCategory ⋙
          tensorRight ((DerivedCategory.singleFunctor _ 0).obj
            (spInternalSignedTwist X.left
              (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
              (spQbarTwist X.left ell) (d : ℤ))) ⋙ shiftFunctor _ (2 * (d : ℤ))).obj K.obj) := by
  sorry
end AlgebraicGeometry.ProEtale
