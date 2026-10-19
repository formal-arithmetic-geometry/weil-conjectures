/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPuritySourceReduction
public import Sheaf.Paper.AdicPurityExceptionalReduction
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.SmoothPurityMap
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.Paper.IntegralExceptionalInverseImage
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.FiniteCoefficientSmoothPurity
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.TwistPreservesFiniteness
import Sheaf.Paper.FiniteReductionOfPurity
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.IntegralCtfTriangulated
import Sheaf.CategoryTheory.SequentialTowerEvaluationFull
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteTorAmplitudeSites
/-! # Adic reconstruction of the specified finite smooth-purity comparisons
Source: blueprint thm-pur-adic-reconstruction, current main-20261015 snapshot.
The source is integral pullback followed by the actual coefficient twist and shift.
The target is the total inverse limit of the actual exceptional coefficient system.
All finite coefficients are those of PurityFiniteSetting.{u}, without a universe lift
of the geometric datum or a divisibility restriction on the coefficient exponent.
(blueprint: thm-pur-adic-reconstruction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

/-- Exact restriction/evaluation comparison induced by the ordinary identity on sections.
Source: blueprint strict tower realization (blueprint: thm-pur-adic-reconstruction). -/
def purAdicRestrictedEvaluation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) (n : ℕ) :
    coefficientSequenceDerivedRestriction l E W ⋙ coefficientConstantTowerEvaluation l E W n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        (scalarReductionRestriction l E W n).mapDerivedCategory :=
  letI := scalarReductionRestrictionLimits l E W n
  letI := scalarReductionRestrictionColimits l E W n
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]


/-- Adic reconstruction of the specified finite smooth-purity arrows.
Source: blueprint thm-pur-adic-reconstruction, current statement and five-step proof
(blueprint: thm-pur-adic-reconstruction).
Proof: integral pullback and the locally free coefficient twist give the actual source,
its uniform constructible and Tor bounds, and its canonical quotient identifications.
Evaluate the strict exceptional system, using the section-normalized site comparisons
and the compact-support adjunction mates, to obtain the actual finite exceptional images.
The finite purity arrows commute with quotient normalization by finite reduction of
purity. After exact scalar restriction, sequential-tower evaluation fullness supplies a
coherent morphism G with the displayed evaluations; no uniqueness of G is asserted.
Take its total derived inverse limit and precompose the derived-completion unit of the
source. The level arrows are isomorphisms by isIso_smoothPurityMap. The natural Roos
triangles then make this limit map invertible. Source finiteness and isomorphism
invariance give target finiteness. Normalized DVR effectivity identifies the target
reduction counits as isomorphisms. Transposing the limit-projection equation under
actual derived scalar extension/restriction proves the displayed quotient-linear
identity, rather than merely asserting that some reduced map is invertible. -/
theorem purAdicReconstruction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) :
    ∃ gamma : purAdicSource D C E f d K ⟶ purAdicTarget D C E f K,
      IsIso gamma ∧
      finiteTorConstructibleIntegral C.l E X (purAdicSource D C E f d K) ∧
      finiteTorConstructibleIntegral C.l E X (purAdicTarget D C E f K) ∧
      (∀ n : ℕ, IsIso (purAdicSourceReduction D C E f d K hK n) ∧
        IsIso (purAdicTargetReduction D C E f d K hK n) ∧
        (scalarReductionDerivedExtension C.l E X n).map gamma ≫
          purAdicTargetReduction D C E f d K hK n =
        purAdicSourceReduction D C E f d K hK n ≫
          (purAdicFiniteArrow D C E f d K hK n).hom) ∧
      ∃ G : (coefficientSequenceDerivedRestriction C.l E X).obj
          ((pullbackTensorCalculus C.l E X).reduction.obj (purAdicSource D C E f d K)) ⟶
        (coefficientSequenceDerivedRestriction C.l E X).obj
          ((integralExceptionalSystem C.l E D C.different f).obj K),
        gamma = (pullbackTensorCalculus C.l E X).adjunction.unit.app _ ≫
          (coefficientConstantTowerLimit C.l E X).map G ∧
        ∀ n : ℕ,
          (coefficientConstantTowerEvaluation C.l E X n).map G ≫
            (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
            (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
              (purAdicExceptionalEvaluation D C E f K n).hom =
          (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
            (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
              (((pullbackTensorCalculus C.l E X).reductionEvaluation n).hom.app _ ≫
                purAdicSourceReduction D C E f d K hK n ≫
                (purAdicFiniteArrow D C E f d K hK n).hom) := by
  sorry

end WeilConjectures
