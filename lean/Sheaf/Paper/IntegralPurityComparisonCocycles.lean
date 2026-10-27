/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.AdicPurityScalarNaturality
public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.FiniteReductionComparisons

/-! # Canonical integral purity comparison equations

Source: six-operations package, clause (6), and purity transport.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.NormalizedIntegralPurityTrace
open AdicPurityScalarNaturality

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (r : ℕ) [SmoothOfRelativeDimension r f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (A : Data D C f r S) (E : Field D C)

set_option maxHeartbeats 800000 in
-- Elaborate the canonical coefficient comparisons with their full dependent endpoints.
/-- The direct and iterated source, exceptional and support comparisons coincide.
Source: six-operations package, clause (6), successive quotient paragraph;
source finiteness, integral exceptional adjunction and compact-support coefficient change
(blueprint: lem-sf-integral-purity-comparison-cocycles).

Proof: substitute the normalization equations for α and c. Identify the two derived
reduction functors by the unique comparison of
left adjoints to composite scalar restriction. The hypothesis is the equality of
actual completed-ring projections, so this comparison is the tensor associator.
The scalar adjunction units identify it with the direct quotient normalization in
purAdicSource_finiteness_reductions. Substitute this into its source square.
For the exceptional square, transpose under compact support and exceptional inverse
image. The coefficient mate preserves the actual counit, so mate pasting identifies
successive reduction with direct reduction. The integral exceptional tower evaluation
has this same normalization, giving the asserted target square. For support, apply
comparison_composition, conjugate by reductionBridge and finiteImageIso, and use
naturality of these isomorphisms. Its finite comparison is exactly the specified
compact-support scalar mate. This proves the support square for every input N,
hence for the two stated inputs. At equal indices the same unit-normalized adjunction
comparison gives the identity quotient equation; no nonempty-scheme assumption enters.
-/
theorem integralPurityComparisonCocycles
    (hprojection : ∀ (W : Scheme.{u}) (n m : ℕ) (h : m ≤ n),
    (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W ≫
      Scheme.proEtaleConstantRingMap (T := W)
        ((purAdicFiniteSetting D C E.val n).finiteReductionRingHom
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h)) =
    (PurCompactSupport.reduction C.l E.val (m + 1) (Nat.succ_pos m)).map W)
    (K : Cat D C E Y)
    (α : ∀ (W : Scheme.{u}) (n m : ℕ) (h : m ≤ n),
      scalarReductionDerivedExtension C.l E.val W n ⋙
        (purAdicFiniteSetting D C E.val n).finiteReduction
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) W ≅
      scalarReductionDerivedExtension C.l E.val W m)
    (hα : α = fun (W : Scheme.{u}) (n m : ℕ) (h : m ≤ n) ↦
      (show scalarReductionDerivedExtension C.l E.val W n ⋙
        (purAdicFiniteSetting D C E.val n).finiteReduction
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) W ≅
      scalarReductionDerivedExtension C.l E.val W m from
        Functor.isoWhiskerRight (reductionBridge D C E W n) _ ≪≫
    PurCompactSupport.tensorComposition
      ((PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n)).map W)
      (Scheme.proEtaleConstantRingMap (T := W)
        ((purAdicFiniteSetting D C E.val n).finiteReductionRingHom
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h)))
      ((PurCompactSupport.reduction C.l E.val (m + 1) (Nat.succ_pos m)).map W)
      (hprojection W n m h) ≪≫
    (reductionBridge D C E W m).symm))
    (c : ∀ (N : DerivedCategory (scalarReductionSource C.l E.val X)) (n : ℕ),
      (scalarReductionDerivedExtension C.l E.val Y n).obj
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f)).obj N) ⟶
      ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).obj
        ((scalarReductionDerivedExtension C.l E.val X n).obj N))
    (hc : c = fun (N : DerivedCategory (scalarReductionSource C.l E.val X)) (n : ℕ) ↦
      (show (scalarReductionDerivedExtension C.l E.val Y n).obj
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
          (integralExceptionalCompactification D f)).obj N) ⟶
      ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).obj
        ((scalarReductionDerivedExtension C.l E.val X n).obj N) from
        (reductionBridge D C E Y n).hom.app _ ≫
  (PurCompactSupport.comparison.{u}
    (PurCompactSupport.reduction C.l E.val (n + 1) (Nat.succ_pos n))
    (integralExceptionalCompactification D f)).app N ≫
  (PurCompactSupport.finiteImageIso.{u} C.l E.val n
    (integralExceptionalCompactification D f)).hom.app _ ≫
  ((purAdicFiniteSetting D C E.val n).smoothCompactSupport f).map
    ((reductionBridge D C E X n).inv.app N))) :
    ∀ (n m : ℕ) (h : m ≤ n),
    ((purAdicFiniteSetting D C E.val n).finiteReduction
      (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) X).map
        (purAdicSourceReduction D C E.val f r K.obj K.property n) ≫
      ((purAdicFiniteSetting D C E.val n).finiteReductionSourceComparison
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f r _).hom ≫
      ((purAdicFiniteSetting D C E.val m).compositionShiftedPullback f r).map
        ((α Y n m h).hom.app K.obj) =
      (α X n m h).hom.app
          (purAdicSource D C E.val f r K.obj) ≫
        purAdicSourceReduction D C E.val f r K.obj K.property m ∧
    ((purAdicFiniteSetting D C E.val n).finiteReduction
      (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) X).map
        (purAdicTargetReduction D C E.val f r K.obj K.property n) ≫
      (purAdicFiniteSetting D C E.val n).finiteReductionExceptionalComparison
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f r _
          (purAdicReductionFiniteTor D C E.val Y K.obj K.property n) ≫
      ((purAdicFiniteSetting D C E.val m).compositionExceptional f).map
        ((α Y n m h).hom.app K.obj) =
      (α X n m h).hom.app
          (purAdicTarget D C E.val f K.obj) ≫
        purAdicTargetReduction D C E.val f r K.obj K.property m ∧
    ∀ N : DerivedCategory (scalarReductionSource C.l E.val X),
      N = purAdicSource D C E.val f r K.obj ∨ N = purAdicTarget D C E.val f K.obj →
      ((purAdicFiniteSetting D C E.val n).finiteReduction
        (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) Y).map
          (c N n) ≫
        (purAdicFiniteSetting D C E.val n).finiteReductionCompactSupportComparison
          (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) f _ ≫
        ((purAdicFiniteSetting D C E.val m).smoothCompactSupport f).map
          ((α X n m h).hom.app N) =
        (α Y n m h).hom.app
            ((PurCompactSupport.image (PurCompactSupport.completed C.l E.val)
              (integralExceptionalCompactification D f)).obj N) ≫
          c N m := by sorry

end WeilConjectures.NormalizedIntegralPurityTrace
