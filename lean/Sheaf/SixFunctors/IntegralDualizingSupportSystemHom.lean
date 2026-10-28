/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.SixFunctors.CoefTowerEvaluationPairingData

/-! # Quotient-system dual of compact support, before any inverse limit

Source: prop-coef-integral-dualizing, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Compact support performed on quotient systems, before integral realization.
The operations are the actual open and proper functors of the pairing frame.
Source: prop-coef-integral-dualizing, second proof paragraph.
(blueprint: def-coef-integral-dualizing-support-system-hom). -/
def integralDualizingSystemSupport
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S) :
    sfIntegralConstructibleCategory l E X ⥤
      coefficientSequenceDerived l E (Spec (.of D.k)) :=
  (sfIntegralConstructible l E X).ι ⋙ S.reduction ⋙
    G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor

/-- Quotient-linear derived Hom from compact support into the coefficient unit,
followed by scalar restriction and derived sections, retaining the strict index.
The target uses the existing base closed structure's tensor unit.
Source: prop-coef-integral-dualizing, the middle finite mapping complex.
(blueprint: def-coef-integral-dualizing-support-system-hom). -/
def integralDualizingSupportSystemHom
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S) :
    (sfIntegralConstructibleCategory l E X)ᵒᵖ ⥤ coefPairingDerived l E :=
  (integralDualizingSystemSupport D l E X S G).op ⋙
    (Functor.curry.obj (coefficientSequenceInternalHom l E (Spec (.of D.k)))).flip.obj
      G.baseTensors.systemClosed.monoidal.tensorUnit ⋙
    coefPairingSections l E (Spec (.of D.k))

end WeilConjectures
