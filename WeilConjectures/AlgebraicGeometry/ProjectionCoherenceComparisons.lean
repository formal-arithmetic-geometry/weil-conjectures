/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum

/-! Canonical comparisons shared by projection coherence and finite reduction.

The definitions are moved verbatim from ProjectionFormulaCoherence, preserving
both their public names and their constructions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The canonical integral tensor-pullback comparison in the datum's coordinates.
This conjugates the recorded representative-normalized comparison by the datum's
functor equalities; it introduces no alternative monoidal comparison.
Source: current blueprint prop-sf-pf-coherence, monoidality identifications
(blueprint: def-sf-projection-coherence-comparisons). -/
def sixFunctorProjectionIntegralMu (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (S.higher.integral.pull f).obj (((S.higher.integralTensor Y).obj K).obj L) ≅
      ((S.higher.integralTensor X).obj ((S.higher.integral.pull f).obj K)).obj
        ((S.higher.integral.pull f).obj L) :=
  letI : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (map_natCast (X.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (X.obj.hom.residueFieldAlgebraMap x)).invertible
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    fun x ↦ (map_natCast (Y.obj.hom.residueFieldAlgebraMap x) C.l) ▸
      ((PurCompactSupport.coefficientPrimeUnit C.l D C.different).map
        (Y.obj.hom.residueFieldAlgebraMap x)).invertible
  eqToIso (congrArg₂ (fun F T ↦ F.obj ((T.obj K).obj L))
    (S.higher.integralPullback f) (S.higher.integralTensorNormalization Y)) ≪≫
    canonicalIntegralPullbackTensor C.l E f.hom.left K L ≪≫
    eqToIso (congrArg₂ (fun F T ↦ ((T.obj (F.obj K)).obj (F.obj L)))
      (S.higher.integralPullback f) (S.higher.integralTensorNormalization X)).symm


/-- Transport the prescribed tensor associator through the datum's tensor equality.
Source: current blueprint prop-sf-pf-coherence, reduction associativity comparison
(blueprint: def-sf-projection-coherence-comparisons). -/
def sixFunctorProjectionTensorAssociator {B : Type v} [Category.{w} B]
    (T T₀ : B ⥤ B ⥤ B) (h : T = T₀)
    (a : ∀ K L N : B, ((T₀.obj ((T₀.obj K).obj L)).obj N) ≅
      ((T₀.obj K).obj ((T₀.obj L).obj N))) (K L N : B) :
    ((T.obj ((T.obj K).obj L)).obj N) ≅ ((T.obj K).obj ((T.obj L).obj N)) :=
  eqToIso (congrArg (fun T ↦ (T.obj ((T.obj K).obj L)).obj N) h) ≪≫
    a K L N ≪≫
    (eqToIso (congrArg (fun T ↦ (T.obj K).obj ((T.obj L).obj N)) h)).symm


end WeilConjectures
