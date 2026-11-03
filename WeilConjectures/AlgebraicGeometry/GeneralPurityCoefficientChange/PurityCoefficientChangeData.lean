/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange

/-!
# Purity and the smooth trace under change of coefficients

The relocated native comparison definitions (blueprint: def-pur-coefficient-change-data).

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-thm-purity-transport-coefficient-change.md`, clauses (1)--(3) and the final
assertion, with its proof (blueprint: det-sp-purity-coefficient-change).

The base is a field `k` that is finite or algebraically closed, with `ringChar k`
prime and different from `ell` (the setting of def-sf-setting).
The adjunction family `A` is any family of explicit restricted adjunctions of
def-pur-general-transport-data (`GeneralTransportData`) that satisfies its
predicates `BrownComparison`, `ScalarCompatible` and `AffineNormalized`: these are
the normalizations of the explicit adjunction of det-sp-comparison-brown-explicit
(counit normalized by affine-line integration and transported along the listed
coefficient changes).  `γ` is computed by `rightAdjointUniq` against the published
Brown restriction, i.e. it is the unique counit-compatible comparison of
det-sp-comparison-brown-unique (the `∃! gamma` clause of `BrownComparison`), and
`Tr = ε ∘ Rf_!(γ)` is the transported counit.  The base-change and composition
predicates and the purity theorem `smooth_purity_transport` are not assumed and its
module is not imported: that theorem's proof (its Step 4) applies this statement.
The coefficient comparisons are the published ones: `b` is
`scalarCompactSupportMap` (proper/open mate), `c` is `scalarExceptionalBeta`
(transpose of `T(ε) ∘ b⁻¹`), and the source map is `sourceScalar` on the
`Coordinates` of `Sheaf.Paper.CondensedPurityCoefficientChange`.

The definitions below are those of
`PurityCoefficientChange.condensed_purity_coefficient_change`
(lem-pur-condensed-purity-coefficient-change), with the finite-field datum
`D` replaced by the general field `k`; `IdentityCoherent` omits the
compact-support identity clause, which constrains no coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.GeneralPurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] in
/-- A finite or algebraically closed base field has finite `ell`-cohomological dimension.
Source: standing setting (blueprint: det-sp-purity-coefficient-change). -/
theorem baseCD (hk : Finite k ∨ IsAlgClosed k) : BaseFieldFiniteCD ell k :=
  hk.elim (fun h ↦ @BaseFieldFiniteCD.of_finite ell _ k _ h)
    (fun h ↦ @BaseFieldFiniteCD.of_isAlgClosed ell _ k _ h)

/-- Multiplication by `q^d`, `q = #k`, on the Tate line (used only for finite `k`).
Source: canonical Tate normalization (blueprint: det-sp-purity-coefficient-change). -/
def powerScalar (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    End (c.line.{u} ell X d) :=
  ((Nat.card k) ^ d) • (𝟙 (c.line.{u} ell X d))

/-- Multiplication by `q^{-d}` on the Tate line.
Source: canonical Tate normalization (blueprint: det-sp-purity-coefficient-change). -/
def tau (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) : End (c.line.{u} ell X d) :=
  Ring.inverse (powerScalar ell k c X d)

/-- The shifted derived Tate datum.
Source: canonical Tate normalization (blueprint: det-sp-purity-coefficient-change). -/
def derivedTau (c : Coefficient ell) (X : Scheme.{u}) (d : ℕ) :
    End (c.derivedLine ell X d) :=
  (shiftFunctor _ (2 * (d : ℤ))).map
    ((DerivedCategory.singleFunctor _ 0).map (tau ell k c X d))

end AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
