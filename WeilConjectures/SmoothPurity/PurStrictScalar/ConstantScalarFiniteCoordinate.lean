/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport

/-! # Tensor and finite balancing part of geometric scalar finite evaluation

Source: Stacks 0B56, 0E8I and 0940.
(blueprint: lem-pur-constant-scalar-finite-coordinate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Scalar comparison on constant towers is compatible with a finite quotient
coordinate. The coordinate is arbitrary and no native reduction calculus occurs.
Source: Stacks 07A6, 0B56, 0E8I and 0940; scalar mates and quotient balancing.
(blueprint: lem-pur-constant-scalar-finite-coordinate).
Proof: transpose the evaluated proper scalar mate under the scalar and geometric
adjunctions. Tensor-unit normalization and the proper counit identify it with
the finite properComparison. For the open factor, both maps are tensor balancing
on the open and zero off it. The finiteOrdinaryBalancing pure-tensor equation
commutes with these units and counits, and its universal cochain equation gives
finiteBalancing after localization. Paste the proper and open equations, moving
the arbitrary coordinate through them by naturality. The finite comparison is
properComparison followed by proper image of openComparison. This calculation
uses simultaneous diagram resolutions, so holds for all derived K and N. -/
theorem constantScalar_finiteCoordinate
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (n : ℕ)
    (K : DerivedCategory
      (Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X))
    (N : DerivedCategory (pbcModules X
      ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)))
    (r : (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj K ≅
      (finiteRestriction l E X n).obj N) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
        ((comparison l E F i c).app K) ≫
      (constantImageEvaluation l F c n).hom.app ((T l E F i X).obj K) ≫
      (PurCompactSupport.image (constants l F) c).map
        ((tensorEvaluation l E F i X n).hom.app K) ≫
      (PurCompactSupport.image (constants l F) c).map
        ((baseTensor l E F i X).map r.hom) ≫
      (PurCompactSupport.image (constants l F) c).map
        ((finiteBalancing l E F i X e he hepos n).hom.app N) ≫
      (positiveImageRestriction l F c (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).hom.app
        ((pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
          (Nat.le_add_left 1 n)).map X)).obj N) =
      (tensorEvaluation l E F i Y n).hom.app ((image l E c).obj K) ≫
      (baseTensor l E F i Y).map
        ((constantImageEvaluation l E c n).hom.app K) ≫
      (baseTensor l E F i Y).map
        ((PurCompactSupport.image (constants l E) c).map r.hom) ≫
      (baseTensor l E F i Y).map
        ((positiveImageRestriction l E c (n + 1) (Nat.le_add_left 1 n)).hom.app N) ≫
      (finiteBalancing l E F i Y e he hepos n).hom.app
        ((PurCompactSupport.image
          (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) c).obj N) ≫
      (positiveRestriction l F Y (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
        ((PurCompactSupport.comparison
          (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
            (Nat.le_add_left 1 n)) c).app N) := by sorry

end WeilConjectures.PurStrictScalar
