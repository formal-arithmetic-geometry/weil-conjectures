/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations

/-! # Completed descent and projection normalization of the scalar-limit comparison

Source: Stacks Tags 0941, 07A6 and 06YY; Steps 3--6 of the normalized
compact-support scalar-limit argument.
(blueprint: lem-pur-compact-support-scalar-limit-completed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- The completed-linear scalar comparison descends the specified three-factor
limit map and satisfies its constant and completed finite-projection equations.
This theorem concerns the comparison map, not effectivity or normalization of the
individual support towers.
Source: Stacks Tags 0941, 07A6, 06YY; parent argument Steps 3--6.
(blueprint: lem-pur-compact-support-scalar-limit-completed-comparison).
Proof: on the full normalized native support towers, finite-free scalar extension
commutes with products. The canonical tensor/limit comparison, the derived strict
scalar mate, and the inverse cofinal restriction therefore give the specified
invertible scalar-limit arrow. Restriction from completed to constant coefficients
is an equivalence on derived-complete objects. Using scalarCompletion and the two
scalarSupportLimit identifications transports this arrow to a unique completed
map. Uniqueness makes the lifted components natural, and reflection of isomorphisms
gives an invertible natural transformation. On the nth retained projection the
cofinal restriction selects e(n+1)-1, its block part has zero projection contribution,
and the tensor comparison tensors each coordinate. The evaluated strict scalar mate
is finiteTensorMap under sourceEvaluation and targetEvaluation. This gives the
constant-coefficient projection equation. The quotient-normalized scalarCompletion
and scalarReductionBalancing transport that equation to completed coefficients:
the scalar adjunction unit sends x to x tensor 1 and balancing multiplies the
last two scalars. The resulting equality is the completed projection equation
with the actual source counit. This uses every positive F-level for completeness;
no fullness of restriction on arbitrary derived objects is asserted. -/
theorem scalarLimitCompletedComparison (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    : ∃ γ : (finiteTorConstructibleIntegral l E X).ι ⋙ scalarSupport l E c S ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y) ⟶
      (finiteTorConstructibleIntegral l E X).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙ scalarSupport l F c S',
      IsIso γ ∧
      ∀ (M : finiteTorConstructibleIntegralCategory l E X),
    ((baseTensor l E F i Y).map
          ((scalarSupportLimit l E c S).hom.app M.obj) ≫
          scalarLimitArrow l E F i c S S' e he hepos M.obj =
        (scalarCompletion l E F i Y).hom.app
            ((scalarSupport l E c S).obj M.obj) ≫
          (scalarConstantRestriction l F Y).map
            (γ.app M) ≫
          (scalarSupportLimit l F c S').hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ∧
    (∀ n : ℕ,
      scalarLimitArrow l E F i c S S' e he hepos M.obj ≫
          (scalarLimitProjection l F Y (e * (n + 1) - 1)).app
            ((support l F c S').obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ≫
          (positiveSupportEvaluation l F c S' (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))).hom.app
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ≫
          (positiveRestriction l F Y (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              ((PurCompactSupport.image (PurCompactSupport.finite l F (e * (n + 1))
                (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).map
                  ((scalarReductionBalancing l E F i X e he hepos n).hom.app M.obj)) =
        (baseTensor l E F i Y).map
            ((scalarLimitProjection l E Y n).app ((support l E c S).obj M.obj) ≫
              (supportEvaluation l E c S n).hom.app M.obj) ≫
          (finiteBalancing l E F i Y e he hepos n).hom.app
            ((PurCompactSupport.image (PurCompactSupport.finite l E (n + 1)
              (Nat.le_add_left 1 n)) c).obj
                ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
                  (Nat.le_add_left 1 n) X)).obj M.obj)) ≫
          (positiveRestriction l F Y (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
              (PurCompactSupport.finiteTensorMap l E F i e he hepos n c M.obj)) ∧
    (∀ n : ℕ,
      γ.app M ≫
          scalarSupportPositiveProjection l F c S' (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n))
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj) ≫
          (pbcDerivedRestrict (PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
            ((PurCompactSupport.image (PurCompactSupport.finite l F (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n))) c).map
                ((scalarReductionBalancing l E F i X e he hepos n).hom.app M.obj)) =
        (pbcDerivedScalarAdjunction (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).unit.app _ ≫
          (pbcDerivedRestrict (PurCompactSupport.projection l F (e * (n + 1))
            (Nat.mul_pos hepos (Nat.le_add_left 1 n)) Y)).map
            ((scalarReductionBalancing l E F i Y e he hepos n).hom.app
                ((scalarSupport l E c S).obj M.obj) ≫
              (pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
                (Nat.le_add_left 1 n)).map Y)).map (scalarSupportCounit l E c S n M.obj) ≫
              PurCompactSupport.finiteTensorMap l E F i e he hepos n c M.obj)) := by
  sorry

end WeilConjectures.PurStrictScalar
