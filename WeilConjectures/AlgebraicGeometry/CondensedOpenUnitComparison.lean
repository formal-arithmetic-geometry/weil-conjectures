/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenCounitUnits

/-! # Geometric open comparison for a fixed coefficient model

Source: purity transport, Steps 2--3; open-counit normalization proof Steps 1--4.
(blueprint: lem-pur-condensed-open-unit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open CondensedERealization CondensedExceptionalReconstruction
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.CondensedOpenCounitRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The specified open comparisons are preserved and satisfy the normalized counit.
This is the geometric part of the parent construction, with the coefficient model fixed.

Source: current blueprint sec-smooth-purity, sk-thm-purity-transport, Steps 2--3;
open-counit normalization proof Steps 1--5
(blueprint: lem-pur-condensed-open-unit-comparison).

Proof: finite type gives Noetherianity, finite dimension and quasi-compactness of j;
the distinct primes make l invertible. Integral compact-support preservation for
(j,id) gives extension preservation. The completed pullback comparison gives
restriction preservation. The normalized factorization identifies the prescribed
integral map with q inverse, and scalar/open tensor normalization proves both
comparison maps invertible. The section-derived open adjunction normalization,
followed by the two triangle identities and naturality, gives the displayed
counit equation after the transported removeIdentity comparison. This statement
leaves the coefficient-family and scalar-unit construction to its separate node.
-/
theorem condensed_open_unit_comparison (C : Models l k) (hC : FactorNormalized l k C)
    (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] :
    ∃ h : Preserves l k U Y j,
      (∀ M : Integral l (Field.{u} l) U.scheme,
        IsIso (integralIdentification l k C U Y j h M) ∧
        IsIso (extensionComparison l k C U Y j h M)) ∧
      CounitNormalized l k C U Y j h := by
  sorry

end WeilConjectures.CondensedOpenCounitRealization
