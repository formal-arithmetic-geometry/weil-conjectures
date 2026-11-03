/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The algebraic inputs to the native exterior-power estimate

Source: sk-p-real-purity, exterior-power maximum and selected determinant-tensor
summand (blueprint: def-rp-native-exterior-certificates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- All simple constituents have a determinant weight bounded above by d.
Source: sk-p-real-purity, application of sk-p-real-rankin to the exterior power
(blueprint: def-rp-native-exterior-certificates). -/
def ConstituentDeterminantBound (M : WeilModule D l X₀)
    (iota : PadicAlgCl l →+* ℂ) (d : ℝ) : Prop :=
  ∀ Q : WeilModule D l X₀, IsNonzeroSimpleSubquotient D l X₀ M Q →
    ∃ v : ℝ, DeterminantWeight D l X₀ Q iota v ∧ v ≤ d

/-- The selected exterior summand supplies an eigenvalue with the specified scaled norm.
This is only algebraic data: it asserts no eigenvalue inequality.
Source: sk-p-real-purity, exterior maximum B+w and selected summand
(blueprint: def-rp-native-exterior-certificates). -/
def ExteriorBoundWitness (M : WeilModule D l X₀)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l)),
    Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
    ∃ (E : WeilModule D l X₀) (B : ℝ) (δ : ULift.{u + 1} (PadicAlgCl l)),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) E.carrier ∧
      NativeCondensedWeil.Real D l X₀ E iota ∧ ¬ IsZero E ∧
      ConstituentDeterminantBound D l X₀ E iota (B + w) ∧
      Module.End.HasEigenvalue (closedOperator D l X₀ E x i hi).hom δ ∧
      ‖iota δ.down‖ ^ 2 =
        ‖iota α.down‖ ^ 2 * (Nat.card (X₀.left.residueField x.val) : ℝ) ^ B

end WeilConjectures.NativeL2
