/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.RealizationCompletedPull
public import Sheaf.Paper.RealizationLocalizedPush
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! # The specified realization comparisons respect adjunctions

Source: Bhatt--Scholze, Remark 6.8.15, and the scalar-unit calculation in the DAG.
(blueprint: lem-weil-pbc-realization-adjoint-comparisons)

The integral adjunction is characterized by its ambient Hom transpose, using
precisely the strict completion unit. The rational assertion retains tensor units
and counits, and the same integral comparison components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option genSizeOf false
set_option genInjectivity false
universe u uC uD uC' uD' vC vD vC' vD'
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {k : Type u} [Field k] {T U : RealizationPullScheme l k}
  {h : T.scheme ⟶ U.scheme}
  {sT : RealizationScalarFunctorData l E T.scheme}
  {sU : RealizationScalarFunctorData l E U.scheme}

/-- Restrict the specified ordinary integral direct image, without completing it.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def RealizationLocalizedPushData.integralPush
    (b : RealizationLocalizedPushData l E h sT sU) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (proEtaleRingDerivedDirectImage h _ _ b.integralPullback) b.integral

/-- The ambient continuous-coefficient adjunction, in the published section coordinates.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationContinuousAdjunction
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  proEtaleRingDerivedAdjunction h (rationalCoefficientSheaf l U.scheme E)
    (rationalCoefficientSheaf l T.scheme E) a.rationalCoefficient

/-- The same specified alpha, with only the scalar-map abbreviation unfolded.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationAdjointAlpha
    (a : RealizationCompletedPullArrow T U h sT sU) :
    a.integralCompleted ⋙
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
          pbcDerivedExtend (sT.scalarMap l E T.scheme)) ≅
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (sU.scalarMap l E U.scheme)) ⋙ a.continuousPull := by
  simpa only [RealizationScalarFunctorData.scalarMap,
    RealizationCompletedPullArrow.integralCompleted, pbcConditionalIntegral,
    RealizationCompletedPullArrow.continuousPull, realizationPullScalarMap,
    Functor.assoc] using
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (ObjectProperty.liftCompιIso _ _ a.completed_mem) _ ≪≫ a.alpha)

/-- The published integral realization comparison in the common scalar coordinates.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationAdjointIntegral {V : Scheme.{u}} [IsNoetherian V]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∀ t : V, IsUnit (l : V.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E V) :
    pbcRationalization V (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        realizationPullRationalScalar l E s ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete V (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (s.scalarMap l E V) := by
  simpa only [realizationPullScalarMap, RealizationScalarFunctorData.scalarMap] using
    realizationPullIntegral l E s

/-- Tensor extension of the actual integral direct image.
Source: BS Remark 6.8.15; rational transport, blueprint order 1306
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationRationalPush (b : RealizationLocalizedPushData l E h sT sU)
    (qAdd : b.integralPush.Additive) (qLin : b.integralPush.Linear (PbcIntegralRing l E)) :=
  letI := qAdd
  letI := qLin
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) b.integralPush

/-- Compatibility with the two adjunctions, expressed by the node's two equations.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def RealizationAdjointEquations
    {C : Type uC} {D : Type uD} {C' : Type uC'} {D' : Type uD'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vC'} C'] [Category.{vD'} D']
    {P : C ⥤ D} {Q : D ⥤ C} {PE : C' ⥤ D'} {QE : D' ⥤ C'}
    (adj : P ⊣ Q) (adjE : PE ⊣ QE) (FU : C ⥤ C') (FT : D ⥤ D')
    (alpha : P ⋙ FT ⟶ FU ⋙ PE) (beta : Q ⋙ FU ⟶ FT ⋙ QE) : Prop :=
  (∀ N : C, FU.map (adj.unit.app N) ≫ beta.app (P.obj N) ≫ QE.map (alpha.app N) =
    adjE.unit.app (FU.obj N)) ∧
  (∀ M : D, FT.map (adj.counit.app M) =
    alpha.app (Q.obj M) ≫ PE.map (beta.app M) ≫ adjE.counit.app (FT.obj M))

/-- The specified beta is the mate of alpha inverse, integrally and after raw
scalar localization. No properness, rational lattice, or idempotent completion is used.
Source: Bhatt--Scholze, Remark 6.8.15; the DAG scalar-adjunction calculation.
(blueprint: lem-weil-pbc-realization-adjoint-comparisons)

Proof:
1. Remove the invertible strict completion units using completed-pull. Ordinary
pullback and direct image preserve the integral full subcategories. Restoring the
units at the end transports precisely the characterized integral adjunction.
2. The finite coefficient normalizations identify the maps with precomposition.
The coefficient square commutes with A to E; localization preserves its numerator
and denominator. Ring-sheaf change adjunction supplies ambient comparisons b and d
for restriction of scalars and pullback and direct image, with compatible adjuncts.
3. The specified comparisons obey r(alpha) j = b inverse P(j) and
r(beta) j = d inverse Q(j), by their localization-unit normalizations.
4. Apply the coefficient-change adjunct equation to the continuous counit, whose
adjunct is identity. Its restricted adjunct is d, so r(epsilonE) b inverse = epsilon P(d).
5. Transpose the proposed counit equation under scalar extension/restriction.
Use step 3, naturality of b, step 3 again, and step 4. Both sides become j epsilon,
by naturality of the ambient integral counit. Injectivity proves the counit equation,
equivalently that beta is the mate of alpha inverse.
6. Transpose the unit composite under the continuous adjunction. Naturality of
its counit, step 5 at PN, naturality of alpha, and the integral triangle identity
make its transpose identity. The continuous unit has the same transpose. Injectivity
proves the unit equation; restore the completion units as in step 1.
7. Extend the actual linear functors and transformations by rational transport.
On a fraction naturality is the integral equality times the inverse denominator.
The tensor units and counits satisfy the triangles componentwise. Every raw object
is integral, and the extended alpha and beta have the displayed integral components,
conjugated by the scalar functor's integral comparison. The two equations therefore
persist for every raw object. -/
theorem realization_adjoint_comparisons
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (T U : RealizationPullScheme l k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))]
    (sT : RealizationScalarFunctorData l E T.scheme)
    (sU : RealizationScalarFunctorData l E U.scheme)
    (a : RealizationCompletedPullArrow T U h sT sU)
    (b : RealizationLocalizedPushData l E h sT sU) :
    ∃ rationalCoefficients : b.rationalPullback = a.rationalCoefficient,
    ∃ adj : a.integralCompleted ⊣ b.integralPush,
    (∀ (N : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))
      (M : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E))
      (f : a.integralCompleted.obj N ⟶ M),
      HEq ((adj.homEquiv N M f).hom)
        ((pbcActualDerivedAdjunction h (pbcIntegralDatum l E)).homEquiv N.obj M.obj
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app N.obj ≫ f.hom))) ∧
    RealizationAdjointEquations adj
      (realizationContinuousAdjunction a)
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (sU.scalarMap l E U.scheme))
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (sT.scalarMap l E T.scheme))
      (realizationAdjointAlpha a).hom
      (b.beta ≫ eqToHom (congrArg (fun c ↦
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
          pbcDerivedExtend (sT.scalarMap l E T.scheme) ⋙
            proEtaleRingDerivedDirectImage h _ _ c) rationalCoefficients)) ∧
    ∃ (qAdd : b.integralPush.Additive) (qLin : b.integralPush.Linear (PbcIntegralRing l E))
      (adjR : a.rationalCompleted ⊣ realizationRationalPush b qAdd qLin),
      (∀ N : PbcRationalCategory U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E),
        adjR.unit.app N =
        (pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          (adj.unit.app N.obj)) ∧
      (∀ M : PbcRationalCategory T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E),
        adjR.counit.app M =
        (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          (adj.counit.app M.obj)) ∧
      ∃ (alphaR : a.rationalCompleted ⋙ realizationPullRationalScalar l E sT ≅
          realizationPullRationalScalar l E sU ⋙ a.continuousPull)
        (betaR : realizationRationalPush b qAdd qLin ⋙ realizationPullRationalScalar l E sU ≅
          realizationPullRationalScalar l E sT ⋙
            proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient),
        (∀ N : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
          alphaR.hom.app ⟨N⟩ =
          (realizationAdjointIntegral sT).hom.app (a.integralCompleted.obj N) ≫
            (realizationAdjointAlpha a).hom.app N ≫
            a.continuousPull.map ((realizationAdjointIntegral sU).inv.app N)) ∧
        (∀ M : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E),
          betaR.hom.app ⟨M⟩ ≫
            (proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient).map
              ((realizationAdjointIntegral sT).hom.app M) =
          (realizationAdjointIntegral sU).hom.app (b.integralPush.obj M) ≫
            b.beta.app M ≫
            (eqToHom (congrArg (fun c ↦ proEtaleRingDerivedDirectImage h _ _ c)
              rationalCoefficients)).app ((pbcDerivedExtend (sT.scalarMap l E T.scheme)).obj
                M.obj)) ∧
        RealizationAdjointEquations adjR (realizationContinuousAdjunction a)
          (realizationPullRationalScalar l E sU) (realizationPullRationalScalar l E sT)
          alphaR.hom betaR.hom := by
  sorry

end WeilConjectures
