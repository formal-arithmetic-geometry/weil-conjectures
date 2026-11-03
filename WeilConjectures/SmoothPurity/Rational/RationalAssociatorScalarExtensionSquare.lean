/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import WeilConjectures.SmoothPurity.Integral.IntegralAssociatorScalarExtensionSquare

/-! # Naturality and scalar extension of the rational associator

Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The rational associator is natural in its three arguments.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: the integral associator is natural, since coherent reduction is faithful and conjugates
it to the natural system associator. Rational maps are sums of localized integral maps and the
rational tensor is computed on localized pure tensors, so naturality localizes. -/
theorem rationalAssociator_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M M' N N' P P' : sfRationalConstructibleCategory l E W}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom ((rationalDerivedTensor l E W).map (Prod.mkHom f g)) h) ≫
      (pullbackTensorRationalAssociator l E W M' N' P').hom =
    (pullbackTensorRationalAssociator l E W M N P).hom ≫
      (rationalDerivedTensor l E W).map
        (Prod.mkHom f ((rationalDerivedTensor l E W).map (Prod.mkHom g h))) := by
  sorry

/-- The rational associator commutes with the prescribed rational tensor scalar comparison.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: every object and both tensor comparisons are localizations of their integral versions,
and scalar extension sends a localized arrow to the localization of its integral scalar
extension. Both composites are the localization of the two composites of
`integralAssociatorScalarExtensionSquare`. -/
theorem rationalAssociatorScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (pullbackTensorRationalAssociator l E W M N P).hom ≫
      (rationalTensorScalarComparison l E L ι W).hom.app
        (M, (rationalDerivedTensor l E W).obj (N, P)) ≫
      (rationalDerivedTensor l L W).map
        (Prod.mkHom (𝟙 ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M))
          ((rationalTensorScalarComparison l E L ι W).hom.app (N, P))) =
    (rationalTensorScalarComparison l E L ι W).hom.app
        ((rationalDerivedTensor l E W).obj (M, N), P) ≫
      (rationalDerivedTensor l L W).map
        (Prod.mkHom ((rationalTensorScalarComparison l E L ι W).hom.app (M, N))
          (𝟙 ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj P))) ≫
      (pullbackTensorRationalAssociator l L W
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          P)).hom := by
  sorry

end WeilConjectures
