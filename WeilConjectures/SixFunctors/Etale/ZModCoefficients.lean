/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# The coefficient ring `ℤ/ℓ` for étale sheaves of modules

The étale sheaves of modules of the six-functor formalism have coefficients in a ring of the
universe `u + 1`. This file fixes the ring `ℤ/n` in that universe, `ULift (ZMod n)`, and the
constant sheaf of `ℤ/n`-modules on a scheme; its underlying abelian sheaf is the constant sheaf
`AlgebraicGeometry.Scheme.constantZMod`.

## Main definitions

- `AlgebraicGeometry.Etale.ZModCoeff`: the ring `ℤ/n` in the universe `u + 1`.
- `AlgebraicGeometry.Etale.constantZModModule`: the constant sheaf of `ℤ/n`-modules.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The ring `ℤ/n` of coefficients, in the universe `u + 1` of the étale sheaves of modules on
schemes of the universe `u`. -/
abbrev ZModCoeff (n : ℕ) : Type (u + 1) := ULift.{u + 1} (ZMod n)

/-- The constant étale sheaf of `ℤ/n`-modules with value `ℤ/n` on a scheme `X`. -/
noncomputable abbrev constantZModModule (X : Scheme.{u}) (n : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZModCoeff.{u} n)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZModCoeff.{u} n))).obj
    (ModuleCat.of (ZModCoeff.{u} n) (ZModCoeff.{u} n))

end AlgebraicGeometry.Etale
