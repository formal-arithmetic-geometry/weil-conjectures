/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedTowerDirectImage
import all WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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

/-! # Completed pullback on the published completed-coefficient categories

Source: Stacks proetale.tex, Tag 099N (2),(5), blueprint order 1261.
(auxiliary; not a blueprint node)
The coefficient structure is fixed on all quotient projections. Ordinary pullback
is its total derived sheafified tensor inverse image. Completion is characterized
by its reflection universal property on the actual intrinsic complete subcategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The original ring-valued presentation of the actual coefficient limit.
Source: blueprint order 1261 (auxiliary; not a blueprint node). -/
abbrev pbcActualCompletedRing (T : Scheme.{u}) :=
  (adicLisseForget T).obj (pbcAdicCompletion T d)

/-- The recorded coefficient structure map, after forgetting commutativity.
Source: Stacks 099N (auxiliary; not a blueprint node). -/
abbrev pbcActualStructureMap : pbcActualCompletedRing d Y ⟶
    (proEtaleSheafDirectImage g RingCat.{u + 1}).obj (pbcActualCompletedRing d X) :=
  ⟨Functor.whiskerRight (completedCoefficientDirectImageMap g d).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

section CompletionPresentation
variable (X)
variable (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

attribute [local irreducible] pbcCompletedComparison

end CompletionPresentation

variable (T : Scheme.{u})

end AlgebraicGeometry.Scheme
