/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.StandardEtale

/-! # Prime-power cyclotomic transition and root-splitting charts

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md`, Proof (1), primitive-root schemes
(blueprint: lem-pur-cyclotomic-tower-charts).

The abbreviations only specialize the existing localization, polynomial and quotient
constructions. All chart maps below are specified on every polynomial representative.
The successor algebra structure is quantified with its defining coefficient map, so the
statement can use the genuine algebra equivalence and tensor product APIs without choosing
a transition map before asserting its existence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Polynomial TensorProduct
open AlgebraicGeometry CategoryTheory Polynomial

namespace CyclotomicTowerCharts

universe u

/-- The base Z[1/ell]. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev base (ell : ℕ) : Type := Localization.Away (ell : ℤ)

/-- The integer cyclotomic polynomial with coefficients localized in the base.
Source: primitive-root schemes, Proof (1) (blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev polynomial (ell n : ℕ) : (base ell)[X] :=
  (Polynomial.cyclotomic (ell ^ n) ℤ).map (algebraMap ℤ (base ell))

/-- C_n = Z[1/ell][T]/(Phi_(ell^n)). Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev ring (ell n : ℕ) : Type := AdjoinRoot (polynomial ell n)

/-- The class z_n of T. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev root (ell n : ℕ) : ring ell n := AdjoinRoot.root (polynomial ell n)

/-- The transition presentation polynomial Y^ell-z_n. Source: primitive-root schemes,
Proof (1) (blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev stepPolynomial (ell n : ℕ) : (ring ell n)[X] := X ^ ell - C (root ell n)

/-- The splitting polynomial Y^(ell^n)-1. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev rootsPolynomial (ell n : ℕ) : (ring ell n)[X] := X ^ (ell ^ n) - 1

end CyclotomicTowerCharts
