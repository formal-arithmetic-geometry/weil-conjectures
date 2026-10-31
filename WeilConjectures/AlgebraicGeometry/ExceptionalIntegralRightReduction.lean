/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction
import WeilConjectures.AlgebraicGeometry.ExceptionalFiniteOperations

/-! # Finite reduction of the fixed exceptional right adjoint

This statement concerns only the right finite reduction comparison. The integral
and finite adjoints and the two endpoint reconstruction equivalences are fixed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived
  exceptionalProSystemDerived exceptionalProLevelDerived
attribute [local semireducible] exceptionalProSystemDerived exceptionalProLevelDerived
  strictEtaleLevelDerived
attribute [local instance] Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

private def reconstructionFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T) (n : ℕ) :
    R.equivalence.functor ⋙ R.evaluation n ⋙
        (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T).ι ≅
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        pbcDerivedExtend (PurCompactSupport.projection l E.carrier (n + 1)
          (Nat.succ_pos n) T) :=
  Functor.isoWhiskerLeft R.equivalence.functor (eqToIso (R.evaluation_eq n)) ≪≫
    Functor.isoWhiskerRight (eqToIso R.reduction)
      (coefficientSequenceDerivedEvaluation l E.carrier T n) ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier T).ι
      (R.calculus.reductionEvaluation n) ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier T).ι
      (PurCompactSupport.finiteReductionIso l E.carrier T n).symm

private def coordinateEvaluation
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology T) (O := integralExceptionalIntegers l E.carrier)
      (ell := integralExceptionalUniformizer l E.carrier)) (n : ℕ) :
    (ExceptionalIntegralReconstruction.coordinates l E.carrier T).functor ⋙
        P.evaluation n ⋙ (integralExceptionalProRealization l E.carrier T n).mapDerivedCategory ≅
      coefficientSequenceDerivedEvaluation l E.carrier T n ⋙
        (sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft _ (integralExceptionalProEvaluationModel l E.carrier T P n) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (eqToIso (integralExceptionalCoordinatesEvaluation l E.carrier T n)) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
    (integralExceptionalProRealization l E.carrier T n).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft _ (integralExceptionalDerivedLevelFixed l E.carrier T n)

private def normalizedFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : ExceptionalIntegralReconstruction.Reconstruction l E.carrier T)
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology T) (O := integralExceptionalIntegers l E.carrier)
      (ell := integralExceptionalUniformizer l E.carrier)) (n : ℕ) :
    R.equivalence.functor ⋙ (ExceptionalIntegralReconstruction.normalized l E.carrier T).ι ⋙
        (ExceptionalIntegralReconstruction.coordinates l E.carrier T).functor ⋙
        P.evaluation n ⋙ (integralExceptionalProRealization l E.carrier T n).mapDerivedCategory ≅
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        pbcDerivedExtend (PurCompactSupport.projection l E.carrier (n + 1)
          (Nat.succ_pos n) T) ⋙
        (sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse :=
  Functor.isoWhiskerLeft
    (R.equivalence.functor ⋙ (ExceptionalIntegralReconstruction.normalized l E.carrier T).ι)
    (coordinateEvaluation l E T P n) ≪≫
    Functor.isoWhiskerRight R.reduction
      (coefficientSequenceDerivedEvaluation l E.carrier T n ⋙
        (sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse) ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier T).ι
      (Functor.isoWhiskerRight
        ((IntegralSystemRealization.calculus l E.carrier T).reductionEvaluation n ≪≫
          (PurCompactSupport.finiteReductionIso l E.carrier T n).symm)
        (sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse)

private def endpointComparison
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    (R : Reconstruction l E T)
    (S : ExceptionalIntegralReconstruction.Reconstruction l E.carrier T)
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology T) (O := integralExceptionalIntegers l E.carrier)
      (ell := integralExceptionalUniformizer l E.carrier)) (n : ℕ) :
    R.equivalence.functor ⋙ R.evaluation n ⋙
        sfFiniteOperationsRealization l E ⟨n + 1, Nat.succ_pos n⟩ T ≅
      S.equivalence.functor ⋙ (ExceptionalIntegralReconstruction.normalized l E.carrier T).ι ⋙
        (ExceptionalIntegralReconstruction.coordinates l E.carrier T).functor ⋙
        P.evaluation n ⋙ (integralExceptionalProRealization l E.carrier T n).mapDerivedCategory :=
  Functor.isoWhiskerRight (reconstructionFiniteReduction l E T R n)
    (sfIntrinsicDerivedEquivalence T
      (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse ≪≫
    (normalizedFiniteReduction l E T S P n).symm

private def systemFiniteRightRealization
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s : ExceptionalIntegralReconstruction.Systems l E.carrier c) (n : ℕ) :
    (s.siteY.image.level n).direct ⋙ s.right.levelRight n ⋙
        (s.siteX.image.level n).inverse ⋙
        (integralExceptionalProRealization l E.carrier X n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E.carrier Y n).mapDerivedCategory ⋙
        ProEtale.sfFiniteExceptionalAt
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E.carrier (n + 1))) c := by
  letI := sfFiniteOperationsEtaleLeftAdjoint l E ⟨n + 1, Nat.succ_pos n⟩ c
  let BX := ExceptionalIntegralReconstruction.Systems.siteRealization l E.carrier X
    s.ordinary.PX s.siteX
  let BY := ExceptionalIntegralReconstruction.Systems.siteRealization l E.carrier Y
    s.ordinary.PY s.siteY
  let H := (Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E.carrier (n + 1)))) c).rightAdjoint
  let U := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E.carrier (n + 1)))) X).mapDerivedCategory
  exact Functor.isoWhiskerLeft ((s.siteY.image.level n).direct ⋙ s.right.levelRight n)
      (integralExceptionalSiteDerivedInverse l E.carrier X s.ordinary.PX BX n) ≪≫
    Functor.isoWhiskerLeft (s.siteY.image.level n).direct
      (Functor.isoWhiskerRight
        (integralExceptionalEtaleRightAdjoint l E.carrier f c s.ordinary n s.right H
          (Adjunction.ofIsLeftAdjoint _)) U) ≪≫
    Functor.isoWhiskerRight
      (integralExceptionalSiteDerivedRight l E.carrier Y s.ordinary.PY BY n) (H ⋙ U)

private theorem finiteRightRealization
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f) (E : FieldStage.{u} l) (n : ℕ)
    (B : Operation.{u} l Ω X Y (.finite E ⟨n + 1, Nat.succ_pos n⟩))
    (leftB : LeftRealization.{u} l Ω c (.finite E ⟨n + 1, Nat.succ_pos n⟩) B) :
    Nonempty (B.G ⋙ sfFiniteOperationsRealization l E ⟨n + 1, Nat.succ_pos n⟩ X ≅
      sfFiniteOperationsRealization l E ⟨n + 1, Nat.succ_pos n⟩ Y ⋙
        ProEtale.sfFiniteExceptionalAt
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E.carrier (n + 1))) c) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ (Y ↘ Spec (.of D.k)))
  obtain ⟨_, _, h⟩ := exists_sfFiniteExceptionalOperations D l hl f c d hd
  obtain ⟨F, G, eF, eG, _, _, _, _, adj, _⟩ := h E ⟨n + 1, Nat.succ_pos n⟩
  let e : F ≅ B.F :=
    ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).fullyFaithfulι
      |>.whiskeringRight _).preimageIso
      (eqToIso eF ≪≫ Functor.isoWhiskerLeft _
        (PurCompactSupport.finiteImageIso l E.carrier n c).symm ≪≫ leftB.symm)
  let g : G ≅ B.G := (adj.ofNatIsoLeft e).rightAdjointUniq B.adjunction
  exact ⟨Functor.isoWhiskerRight g.symm
      (sfFiniteOperationsRealization l E ⟨n + 1, Nat.succ_pos n⟩ X) ≪≫
    sfFiniteOperationsRightRealization l E ⟨n + 1, Nat.succ_pos n⟩ c G eG⟩

/-- Finite reduction commutes with the fixed integral exceptional right adjoint.
Source: Zheng, Construction 4.1, Lemma 5.22 and Propositions 5.24 and 5.26(3).
(blueprint: lem-sf-exceptional-integral-right-reduction)

Proof: the reconstruction reduction and evaluation equations identify each
endpoint composite with actual derived extension to the positive finite quotient.
Transport the ordinary etale strict-system exceptional adjunction through the
etale/pro-etale comparison, as in exceptionalSystemTransport. Lemma 5.22 identifies
its finite evaluations and quotient mates with the finite exceptional adjoints;
Proposition 5.24 preserves normalization. Restrict to the common constructible,
cohomological and Tor bounds and apply the actual reduction/limit equivalence.
The supplied left realizations identify the resulting integral and finite left
functors with the fixed ones. Uniqueness of their right adjoints then identifies
the right functors, and Proposition 5.26(3) gives the displayed natural reduction
isomorphism. Use the actual unit and counit in these identifications, so all
comparisons exist on whole systems and no faithfulness of finite evaluation is
asserted. Empty schemes give the zero comparison; n always means exponent n+1. -/
theorem exists_exceptional_integral_right_reduction
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (E : FieldStage.{u} l)
    (integral : Operation.{u} l Ω X Y (.integral E))
    (finite : ∀ n : ℕ, Operation.{u} l Ω X Y (.finite E ⟨n + 1, Nat.succ_pos n⟩))
    (leftIntegral : LeftRealization.{u} l Ω c (.integral E) integral)
    (leftFinite : ∀ n : ℕ,
      LeftRealization.{u} l Ω c (.finite E ⟨n + 1, Nat.succ_pos n⟩) (finite n))
    (RX : Reconstruction l E X) (RY : Reconstruction l E Y) :
    Nonempty (∀ n : ℕ,
      integral.G ⋙ RX.equivalence.functor ⋙ RX.evaluation n ≅
        RY.equivalence.functor ⋙ RY.evaluation n ⋙ (finite n).G) := by
  classical
  obtain ⟨_, rX, rY, s, a, ⟨d⟩⟩ :=
    ExceptionalIntegralReconstruction.exceptionalIntegralReconstruction l E.carrier D hl f c
  let eF : integral.F ≅
      ExceptionalIntegralReconstruction.integralLeft l E.carrier c rX rY s a :=
    ((finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι
      |>.whiskeringRight _).preimageIso (leftIntegral ≪≫ d.realization.symm)
  let eG : integral.G ≅
      ExceptionalIntegralReconstruction.integralRight l E.carrier c rX rY s a :=
    (integral.adjunction.ofNatIsoLeft eF).rightAdjointUniq
      (ExceptionalIntegralReconstruction.integralAdjunction l E.carrier c rX rY s a)
  refine ⟨fun n ↦ ?_⟩
  let qX := endpointComparison l E X RX rX s.siteX.proEvaluation n
  let qY := endpointComparison l E Y RY rY s.siteY.proEvaluation n
  let qFinite := Classical.choice
    (finiteRightRealization l Ω D hl f c E n (finite n) (leftFinite n))
  let H := ProEtale.sfFiniteExceptionalAt
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E.carrier (n + 1))) c
  exact ((finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) X).fullyFaithfulι
    |>.comp (Functor.FullyFaithful.ofFullyFaithful
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse)
    |>.whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft integral.G qX ≪≫
        Functor.isoWhiskerRight eG _ ≪≫
        Functor.isoWhiskerRight
          (ExceptionalIntegralReconstruction.rightEvaluation l E.carrier c rX rY s a n)
          (integralExceptionalProRealization l E.carrier X n).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft
          (rY.equivalence.functor ⋙ (ExceptionalIntegralReconstruction.normalized l E.carrier Y).ι ⋙
            (ExceptionalIntegralReconstruction.coordinates l E.carrier Y).functor ⋙
            s.siteY.proEvaluation.evaluation n) (systemFiniteRightRealization l E c s n) ≪≫
        Functor.isoWhiskerRight qY.symm H ≪≫
        Functor.isoWhiskerLeft (RY.equivalence.functor ⋙ RY.evaluation n)
          qFinite.symm)

end WeilConjectures.ExceptionalIntegralScalar
