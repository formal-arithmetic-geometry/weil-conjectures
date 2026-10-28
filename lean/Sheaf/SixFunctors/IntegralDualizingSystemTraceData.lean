/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSystemAdjunctionMap
public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-! # Finite-counit normalization of a quotient-system trace

The normalization uses the supplied dualizing identifications eQ. It does not
choose arbitrary isomorphisms of compact-support values.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-dualizing-trace-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite etale dualizing complex belongs to D+.
Source: bounded-below preservation by the etale exceptional adjoint
(blueprint: def-coef-system-dualizing-trace-data).
Proof: apply exceptional D+ preservation to the coefficient unit in degree zero. -/
theorem integralDualizingFiniteEtalePlus (n : ℕ) :
    DerivedCategory.TStructure.t.plus (finiteDualizingEtaleTerm l E D X n) := by
  let := (finiteDualizingCompactification D X).hasCompactification
  exact Etale.plus_rightDerivedUpperShriek_obj
    (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) (X ↘ Spec (.of D.k)) _
    (Etale.boundaryCoefficientPlus (finiteDualizingCoeff l E n) (Spec (.of D.k))).property

/-- Transport the ordinary etale exceptional counit using the fixed dualizing
origin and the specified compact-support site comparison.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-dualizing-trace-data). -/
def integralDualizingFiniteSystemCounit (n : ℕ) :
    (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (n + 1))).obj
        (integralDualizingFiniteTerm l E D X n) ⟶
      (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
        (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))) :=
  (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
      (Padic.coefficientExtensionRing l E (n + 1))).map
        (finiteDualizingOrigin l E D X n).inv ≫
    (ProEtale.sfIntrinsicCompactSupportComparison
      (Padic.coefficientExtensionRing l E (n + 1))
      (finiteDualizingCompactification D X)).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
          X).mapDerivedCategory.obj (finiteDualizingEtaleTerm l E D X n)) ≫
    (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))).functor.map
        ((ProEtale.compactSupportSiteComparison (finiteDualizingCoeff l E n)
          (finiteDualizingCompactification D X)).hom.app
            ⟨finiteDualizingEtaleTerm l E D X n, integralDualizingFiniteEtalePlus D l E X n⟩) ≫
    (finiteDualizingRealization l E (Spec (.of D.k)) n).map
      (finiteDualizingEtaleCounit l E D X n)

/-- Data for a trace on a single quotient-system object. Its finite normalizations
are tied to eQ before any test input K is introduced. supportComparison is natural
on the whole system category, rather than an arbitrary isomorphism at Q.
Source: compatibility of the exceptional counits with reduction in
prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-dualizing-trace-data). -/
structure IntegralDualizingSystemTraceData
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n) where
  supportComparison : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) (finiteDualizingCompactification D X).g
  unitEvaluation : ∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj
      G.baseTensors.systemClosed.monoidal.tensorUnit ≅
    (finiteDualizingRealization l E (Spec (.of D.k)) n).obj
      (Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k)))
  trace : G.properModules.rightDerivedFunctor.obj
      (G.openModules.mapDerivedCategory.obj (coefTraceInput l E X Q)) ⟶
    G.baseTensors.systemClosed.monoidal.tensorUnit
  trace_evaluation : ∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map trace ≫
        (unitEvaluation n).hom =
      (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).map
          (supportComparison.hom.app (coefTraceInput l E X Q)) ≫
        (compactSupportSystemEvaluation l E (finiteDualizingCompactification D X) n).hom.app
          (coefTraceInput l E X Q) ≫
        (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
          (Padic.coefficientExtensionRing l E (n + 1))).map (eQ n).hom ≫
        integralDualizingFiniteSystemCounit D l E X n

/-- The comparison obtained from the trace by the two actual adjunction transposes.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-dualizing-trace-data). -/
def integralDualizingSystemAdjunctionMap
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (t : G.properModules.rightDerivedFunctor.obj
        (G.openModules.mapDerivedCategory.obj (coefTraceInput l E X Q)) ⟶
      G.baseTensors.systemClosed.monoidal.tensorUnit) :
    (sfIntegralConstructible l E X).ι.op ⋙ coefPairingHom l E X S Q ⟶
      integralDualizingSupportSystemHom D l E X S G where
  app K := CoefPairingFrame.exceptionalMap S.systemClosed G.baseTensors.systemClosed G.frame
    (coefTraceInput l E X Q) G.baseTensors.systemClosed.monoidal.tensorUnit t
      (S.reduction.obj K.unop.obj)
  naturality K L f := CoefPairingFrame.exceptionalMap_naturality
    S.systemClosed G.baseTensors.systemClosed G.frame (coefTraceInput l E X Q)
      G.baseTensors.systemClosed.monoidal.tensorUnit t
        (S.reduction.obj L.unop.obj) (S.reduction.obj K.unop.obj)
        (S.reduction.map f.unop.hom)

end WeilConjectures
