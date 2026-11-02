/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube

/-!
# The counit-defined diagonal comparison in a base-change cube

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, Proof (1),
first diagonal base-change comparison (blueprint: lem-sp-diagonal-exchange-cube).

The ordinary finite-coefficient comparison is expressed through the canonical
etale-origin coordinates supplied by `diagonalCubeComparisons`.  The theorem
below records the full finite-or-algebraically-closed field statement; its proof
is postponed at stage 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- The diagonal-exchange cube statement over a finite or algebraically closed field.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, Proof (1),
first diagonal base-change comparison (blueprint: lem-sp-diagonal-exchange-cube).
The local instances make the finite-type hypotheses on the displayed schemes
available to the canonical comparison interface.  The two equations, the
specified counit mates, their etale-origin witness condition, smooth relative
dimension, regular diagonal condition, and all identity/zero-dimensional cases
are the clauses of `diagonalCubeComparisons`.
-/
def generalizedDiagonalExchangeCubeStatement
    (k : Type u) [Field k] (_hfield : Finite k ∨ IsAlgClosed k)
    (ell r d : ℕ) [Fact ell.Prime] (_hchar : ell ≠ ringChar k)
    (_hr : 1 ≤ r) {X Y Y' : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (v : Y' ⟶ Y) (aY' : Y' ⟶ Spec (.of k))
    [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (_hv : v ≫ aY = aY') : Prop :=
  letI : Smooth f := SmoothOfRelativeDimension.smooth d f
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : IsNoetherian Y := {}
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := {}
  letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian aY'
  letI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace aY'
  letI : IsNoetherian Y' := {}
  diagonalCubeComparisons (ULift.{u + 1} (ZMod (ell ^ r))) f v d

/-- The counit-defined diagonal comparison commutes with arbitrary change of base.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md`, Proof (1),
first diagonal base-change comparison (blueprint: lem-sp-diagonal-exchange-cube).
Proof: identify the primed self-product with the base change of the original
self-product; use smooth relative-dimension permanence and regularity of the
smooth diagonal; transport finite constructible objects to etale-origin
coordinates; paste the counit-defined exceptional exchanges in the two
factorizations of the Cartesian cube; then restrict along the diagonal and
cancel the canonical pullback and section compositors.  The same equations
include identity base change, relative dimension zero, empty schemes, r = 1,
and arbitrary (possibly nonflat) base change.
-/
theorem generalizedDiagonalExchangeCube
    (k : Type u) [Field k] (hfield : Finite k ∨ IsAlgClosed k)
    (ell r d : ℕ) [Fact ell.Prime] (hchar : ell ≠ ringChar k)
    (_hr : 1 ≤ r) {X Y Y' : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (v : Y' ⟶ Y) (aY' : Y' ⟶ Spec (.of k))
    [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (hv : v ≫ aY = aY') : generalizedDiagonalExchangeCubeStatement
      k hfield ell r d hchar _hr aY f v aY' hv := by
  sorry

end WeilConjectures
