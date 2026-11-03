/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
public import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Explicit coordinates for integral projection

Source: prop-sf-pf-coherence.proof.md, compactification independence; the normalized
reduction/limit adjunction and the specified compact-support construction.
(blueprint: def-sf-integral-projection-coordinate-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification.Coordinates
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]

/-- Inverse of the actual reconstruction unit on the constructible category.
Source: normalized reconstruction (blueprint: def-sf-integral-projection-coordinate-data). -/
def reconstruction (W : Scheme.{u}) (K : sfIntegralConstructibleCategory C.l E W) :
    (coefficientSequenceLimit C.l E W).obj ((calculus C.l E W).reduction.obj K.obj) ≅
      K.obj := by
  have hi : IsIso ((calculus C.l E W).adjunction.unit.app K.obj) := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (C.l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let D₀ : FiniteFieldDatum.{0} :=
      { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_rfl
        cardinality_eq := (pow_one p).symm, k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have h₀ : C.l ≠ D₀.p := by change C.l ≠ p; omega
    have hc : IntegralOnSlice.IsComplete C.l E W none K.obj :=
      ⟨D₀, h₀, (sfDerivedComplete_iff_legacy C.l E W D₀ h₀ K.obj).1 K.property.1⟩
    exact (purNormalizedReconstructionOfScheme C.l E W (calculus C.l E W)).2 K.obj hc
  letI := hi
  exact (asIso ((calculus C.l E W).adjunction.unit.app K.obj)).symm

/-- Reduction of completed tensor as a natural isomorphism, using the specified Roos
comparison and actual reconstruction counit. Source: Stacks 0941 and 07A4
(blueprint: def-sf-integral-projection-coordinate-data). -/
def tensorReductionIso (W : Scheme.{u}) :
    integralCompletedTensor C.l E W ⋙ (calculus C.l E W).reduction ≅
      ((calculus C.l E W).reduction.prod (calculus C.l E W).reduction) ⋙
        (calculus C.l E W).systemClosed.tensor := by
  let A := calculus C.l E W
  let Q := (A.reduction.prod A.reduction) ⋙ A.systemClosed.tensor
  have hc (P : Integral C.l E W × Integral C.l E W) :
      IsIso (A.adjunction.counit.app (Q.obj P)) := by
    have h : IsIso (A.adjunction.counit.app
        (A.reduction.obj (A.integralClosed.tensor.obj P))) :=
      ((purNormalizedReconstructionOfScheme C.l E W A).1 _ (A.reduction_normalized _)).2
    exact (NatTrans.isIso_app_iff_of_iso A.adjunction.counit (A.reductionTensor.app P)).1 h
  letI := hc
  exact Functor.isoWhiskerRight (pullbackTensorIntegralTensorModel C.l E W) A.reduction ≪≫
    NatIso.ofComponents (fun P ↦ asIso (A.adjunction.counit.app (Q.obj P)))
      (fun v ↦ A.adjunction.counit.naturality (Q.map v))

/-- Reduction of completed pullback in the specified whole-system coordinates.
Source: Stacks 0941 and 099N
(blueprint: def-sf-integral-projection-coordinate-data). -/
def pullReduction (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Integral C.l E Y) :
    (calculus C.l E X).reduction.obj ((integralDerivedPullback C.l E f).obj L) ≅
      (pull C.l E f).obj ((calculus C.l E Y).reduction.obj L) := by
  let A := calculus C.l E X
  let Q := (pull C.l E f).obj ((calculus C.l E Y).reduction.obj L)
  have hc : IsIso (A.adjunction.counit.app
      (A.reduction.obj ((PurCompactSupport.pull (PurCompactSupport.completed C.l E) f).obj
        L))) :=
    ((purNormalizedReconstructionOfScheme C.l E X A).1 _ (A.reduction_normalized _)).2
  letI : IsIso (A.adjunction.counit.app Q) :=
    (NatTrans.isIso_app_iff_of_iso A.adjunction.counit
      ((z.realizationModel.reductionPull f).app L)).1 hc
  exact A.reduction.mapIso ((pullbackTensorIntegralPullbackModel C.l E f).app L) ≪≫
    asIso (A.adjunction.counit.app Q)

variable {D C E}

/-- The base prime remains invertible in every residue field.
Source: the base structure map
(blueprint: def-sf-integral-projection-coordinate-data). -/
@[instance_reducible] def residueUnits (hl : IsUnit (C.l : D.k)) (X : SixFunctorSpace D) :
    ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦ by
  let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.obj.hom.appTop ≫
    X.obj.left.Γevaluation x).hom
  exact (Eq.mp (congrArg IsUnit (map_natCast φ C.l)) (hl.map φ)).invertible

variable (D C E)

/-- The datum's pullback has exactly the ambient completed-pullback value.
Source: integralPullback (blueprint: def-sf-integral-projection-coordinate-data). -/
def pullValue (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    ((H.integral.pull f).obj L).obj ≅ (integralDerivedPullback C.l E f.hom.left).obj L.obj := by
  letI := residueUnits hl X
  letI := residueUnits hl Y
  exact eqToIso (congrArg (fun P ↦ (P.obj L).obj) (H.integralPullback f))

/-- The natural reduction comparison for the datum's tensor.
Source: completed tensor normalization
(blueprint: def-sf-integral-projection-coordinate-data). -/
def datumTensorReductionIso (H : SixFunctorHigherOperations D C E)
    (hl : IsUnit (C.l : D.k)) (X : SixFunctorSpace D) :
    Functor.uncurry.obj (H.integralTensor X) ⋙
        (sfIntegralConstructible C.l E X.obj.left).ι ⋙
          (calculus C.l E X.obj.left).reduction ≅
      (((sfIntegralConstructible C.l E X.obj.left).ι ⋙
        (calculus C.l E X.obj.left).reduction).prod
          ((sfIntegralConstructible C.l E X.obj.left).ι ⋙
            (calculus C.l E X.obj.left).reduction)) ⋙
        (calculus C.l E X.obj.left).systemClosed.tensor := by
  letI := residueUnits hl X
  let F := (sfIntegralConstructible C.l E X.obj.left).ι
  let R := (calculus C.l E X.obj.left).reduction
  exact eqToIso (congrArg (fun T ↦ Functor.uncurry.obj T ⋙ F ⋙ R)
      (H.integralTensorNormalization X)) ≪≫
    Functor.isoWhiskerRight
      (Functor.currying.counitIso.app (constructibleIntegralTensor C.l E X.obj.left))
      (F ⋙ R) ≪≫
    Functor.isoWhiskerLeft (F.prod F) (tensorReductionIso D C E X.obj.left)

/-- Reduction of a datum tensor, in canonical system tensor coordinates.
Source: the preceding natural comparison
(blueprint: def-sf-integral-projection-coordinate-data). -/
abbrev datumTensorReduction (H : SixFunctorHigherOperations D C E)
    (hl : IsUnit (C.l : D.k)) (X : SixFunctorSpace D)
    (K L : sfIntegralConstructibleCategory C.l E X.obj.left) :=
  (datumTensorReductionIso D C E H hl X).app (K, L)

/-- Reduction of the projection's tensor/pullback input, with no choice of witness.
Source: tensor and pullback quotient-tower comparisons
(blueprint: def-sf-integral-projection-coordinate-data). -/
def inputReduction (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (calculus C.l E X.obj.left).systemClosed.tensor.obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj,
          (pull C.l E f.hom.left).obj ((calculus C.l E Y.obj.left).reduction.obj L.obj)) ≅
      (calculus C.l E X.obj.left).reduction.obj
        ((((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)).obj) :=
  ((calculus C.l E X.obj.left).systemClosed.tensor.mapIso
    (Iso.prod (Iso.refl _) ((pullReduction D C E o z f.hom.left L.obj).symm ≪≫
      ((calculus C.l E X.obj.left).reduction.mapIso (pullValue D C E H hl f L)).symm))) ≪≫
    (datumTensorReduction D C E H hl X K ((H.integral.pull f).obj L)).symm

/-- Direct support coordinates: proper/limit conjugation, the open reduction mate,
inverse reconstruction unit, the published qcqs realization, and the datum value equality.
Source: compactification realization, steps 3--4
(blueprint: def-sf-integral-projection-coordinate-data). -/
def supportValue (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (coefficientSequenceLimit C.l E Y.obj.left).obj
      ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj))) ≅
      ((H.integral.support f c).obj K).obj := by
  letI := residueUnits hl X
  have hK : finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
    rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact K.property
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨hred, hunit⟩ := GeneratorReduction.openReconstructionEffectivity C.l E o
    z.realizationModel c.i K.obj (Or.inl hK)
  letI := hred
  letI := hunit
  exact (z.realizationModel.push C.l E c.g).app _ ≪≫
    (PurCompactSupport.push (PurCompactSupport.completed C.l E) c.g).mapIso
      ((coefficientSequenceLimit C.l E c.Z).mapIso
        (asIso ((z.realizationModel.openReduction C.l E c.i).app K.obj)) ≪≫
        (asIso ((calculus C.l E c.Z).adjunction.unit.app
          ((ringedOpen C.l E c.i).obj K.obj))).symm) ≪≫
    (sfQcqsCompactSupportRealization C.l E D.k hl c).app K ≪≫
    (sfIntegralConstructible C.l E Y.obj.left).ι.mapIso
      (eqToIso ((sfCompactSupportFiniteIntegralFunctor_obj C.l D.k hl c E K).trans
        ((H.supportConstruction f hl c).choose_spec.2.2.1 K).symm))

/-- The support reduction map is the adjoint of the inverse of the explicit support
value comparison. Its data is constructed before any assertion of invertibility.
Source: reduction/limit adjunction
(blueprint: def-sf-integral-projection-coordinate-data). -/
def supportReduction (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :=
  ((calculus C.l E Y.obj.left).adjunction.homEquiv _ _).symm
    (supportValue D C E H hl o z f c K).inv

/-- Reduction coordinate of the source of one compactification projection.
Source: the tensor of the support comparison
(blueprint: def-sf-integral-projection-coordinate-data). -/
def sourceMap (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  (datumTensorReduction D C E H hl Y ((H.integral.support f c).obj K) L).hom ≫
    (calculus C.l E Y.obj.left).systemClosed.tensor.map
      (Prod.mkHom (supportReduction D C E H hl o z f c K) (𝟙 _))

/-- Reduction coordinate of the target of one compactification projection.
Source: support of the tensor/pullback input comparison
(blueprint: def-sf-integral-projection-coordinate-data). -/
def targetMap (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  supportReduction D C E H hl o z f c
      (((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)) ≫
    (Operations.shriek C.l E o c.i ⋙ Operations.push C.l E o c.g).map
      (inputReduction D C E H hl o z f K L).inv

end WeilConjectures.FixProjectionCompactification.Coordinates
