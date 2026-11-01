/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

/-!

# The fibre product of the strictly local model and the product `X ⨯ X`

This file sets up the identification of `X × X` with the fibre product
`X ×_k X` of the classical model, with the factors interchanged
(`ProEtale.CondensedRing.swapPullbackToProd`): the library's correspondences have support
`(c₁, c₂)` and coefficients `K ⊠ D_X K`, the classical model
(`Etale.CurveLocalModel`) the transposed graph `(h, id)` and `D_X K ⊠ K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-- The identification `X ×_k X ≅ (X ⨯ X).left` interchanging the factors: the first projection
of `X ⨯ X` corresponds to the second projection of the fibre product. -/
noncomputable def swapPullbackToProd (X : Over (Spec (.of k))) :
    pullback X.hom X.hom ⟶ (X ⨯ X).left :=
  (pullbackSymmetry X.hom X.hom).hom ≫ (Over.prodLeftIsoPullback X X).inv

instance (X : Over (Spec (.of k))) : IsIso (swapPullbackToProd X) := by
  unfold swapPullbackToProd
  infer_instance

@[reassoc (attr := simp)]
lemma swapPullbackToProd_fst (X : Over (Spec (.of k))) :
    swapPullbackToProd X ≫ (prod.fst : X ⨯ X ⟶ X).left = pullback.snd X.hom X.hom := by
  simp [swapPullbackToProd]

@[reassoc (attr := simp)]
lemma swapPullbackToProd_snd (X : Over (Spec (.of k))) :
    swapPullbackToProd X ≫ (prod.snd : X ⨯ X ⟶ X).left = pullback.fst X.hom X.hom := by
  simp [swapPullbackToProd]

end AlgebraicGeometry.ProEtale.CondensedRing
