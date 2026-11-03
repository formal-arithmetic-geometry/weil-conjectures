/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.SmoothPurity.GeometricFrobeniusTransport.GeometricFrobeniusCohomologyTransport
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Finite Weil cohomology and a common finite degree support

Source: latest blueprint, det-thm-tf-uniform-formula-weil.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.WeilUniformTrace

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- Finite cohomology and a common finite support, without a trace identity.
Source: latest blueprint, det-thm-tf-uniform-formula-weil.proof.md, clause (1)
(blueprint: lem-wutf-cohomology-finiteness).

Proof: the two strict Weil conventions use the same geometric automorphism. Rational
Dctf equals Dbc on the separated finite-type geometric fiber, so the uniform trace
theorem's perfectness assertion applies to K, without an integral lattice.
Identify its compact-support and point-section complexes with the displayed ones
by the exact/total-derived comparisons and canonical compactification comparison.
Their scalar ring Γ of the constant coefficient condensed ring is the coefficient
field: evaluation at the one-point space inverts constant sections. A bounded
finite-projective representative therefore has finite cohomology, vanishing
outside its finite degree interval. The extension-point scheme over F_(q^m) has
finitely many rational points, since it is of finite type over that finite field.
Take the union of the compact degree interval and the finitely many stalk degree
intervals. Each interval and this union are finite. Outside it all the indicated
cohomology objects are zero. Empty point sets contribute the empty union. -/
theorem cohomology_finiteness (c : WeilCoefficient ell)
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (m : ℕ) (hm : 1 ≤ m) :
    Finite (D.extensionPoints X₀ m hm) ∧
    (∀ i : ℤ, Module.Finite (scalars ell c) (compactCohomology D ell hEll X₀ c c₀ K i)) ∧
    (∀ (y : D.extensionPoints X₀ m hm) (i : ℤ),
      Module.Finite (scalars ell c) (stalkCohomology D ell hEll X₀ c K m hm y i)) ∧
    ∃ s : Finset ℤ,
      (∀ i : ℤ, i ∉ s → IsZero (compactCohomology D ell hEll X₀ c c₀ K i)) ∧
      (∀ (y : D.extensionPoints X₀ m hm) (i : ℤ), i ∉ s →
        IsZero (stalkCohomology D ell hEll X₀ c K m hm y i)) := by
  sorry

end WeilConjectures.WeilUniformTrace
