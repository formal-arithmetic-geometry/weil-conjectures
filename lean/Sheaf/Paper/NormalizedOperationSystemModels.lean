/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SystemCochainTensorReduction
import Sheaf.Paper.CanonicalCoefficientSystemGeometry
import Sheaf.Paper.GeometricScalarAssociationCocycle
import all Sheaf.Paper.SystemTensorReductionFormula
import all Sheaf.Paper.SemilinearSystemModels
import all Sheaf.Paper.SystemOrdinaryTensorReduction
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Sheaf.Paper.SystemEvaluationFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all Sheaf.Paper.KFlatRingedToposPullback

/-! # Normalized operations and simultaneous system models

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0D6D, 06YS, 07A2,
0G7E and 07A6 (blueprint: lem-pur-normalized-operation-system-models).

## Main definitions and statements

- `OperationTensorLaws`, `OperationPullLaws`: actual adjoints and quotient coherence.
- `OperationUnitLaws`: the regular whole-system unit and its multiplication adjoint.
- `OperationModelLaws`: simultaneous resolution and closure of representative models.
- `CoefficientsIdentified`: normalization by the actual constant-section ring maps.
- `normalizedOperationSystemModels`: all operation and simultaneous-model assertions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Retain the recorded localization instances during elaboration.
attribute [local irreducible] WeilConjectures.SemilinearSections.hasDerived
  HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open WeilConjectures.SemilinearSections
namespace WeilConjectures.NormalizedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The existing calculus for the actual positive finite quotient sheaves.
Source: Stacks 07A4, Zheng 4.1 (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev Calculus := SemilinearDerivedSectionsData.{t + 1, t, u}
  (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
  (coefficientSequenceCommRingTransition l E W)

/-- The recorded ordinary localization of whole semilinear systems.
Source: Stacks 05RU (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev Whole := DS.{t + 1, t, max u (t + 1)}
  (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
  (coefficientSequenceCommRingTransition l E W)

/-- The actual sequence-site commutative coefficient sheaf.
Source: Zheng 4.1 (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev WholeRing := systemRing.{t + 1, t, max u (t + 1)}
  (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
  (coefficientSequenceCommRingTransition l E W)

/-- The ordinary module category of whole systems, before localization.
Source: Zheng 4.1 (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev WholeModules := Systems.{t + 1, t, max u (t + 1)}
  (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
  (coefficientSequenceCommRingTransition l E W)

/-- Actual level evaluation, derived after the whole-system localization.
Source: Zheng 4.1 (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev level (n : ℕ) := e.{t + 1, t, max u (t + 1)}
  (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
  (coefficientSequenceCommRingTransition l E W) n

/-- The underlying geometric inverse image, at the coefficient universe.
Source: Stacks 09A5, 00VC (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev inverse {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.proEtaleBaseChange f)
    (Type (max u (t + 1))) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The actual sectionwise geometric direct image.
Source: Stacks 09A5, 00VC (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev direct {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (Scheme.proEtaleBaseChange f).sheafPushforwardContinuous (Type (max u (t + 1)))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical geometric adjunction at the coefficient universe.
Source: Stacks 09A5, 00VC (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev geometricAdjunction {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.proEtaleBaseChange f)
    (Type (max u (t + 1))) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

end WeilConjectures.NormalizedOperations

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The recorded scalar-extension functor, with all instance arguments retained.
Source: Stacks 06YY (blueprint: lem-pur-normalized-operation-system-models). -/
def operationScalarFunctor {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} J S :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.E
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

/-- Termwise extension with its recorded additive witness made explicit.
Source: Stacks 06YY (blueprint: lem-pur-normalized-operation-system-models). -/
def operationScalarComplex {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :=
  letI : (operationScalarFunctor.{c, v, r} J φ A).Additive :=
    @SheafOfModules.DerivedChangeOfRingsCochainModel.additive
      C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
      (abelianSheafify.{c, v, max c v r} J) R S φ
      (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model
  (operationScalarFunctor.{c, v, r} J φ A).mapHomologicalComplex (.up ℤ)

/-- The actual universal derived counit of scalar extension, at the chosen sizes.
Source: Stacks 06YY (blueprint: lem-pur-normalized-operation-system-models). -/
def operationScalarCounit {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    DerivedCategory.Q ⋙ A.T ⟶
      operationScalarComplex.{c, v, r} J φ A ⋙ DerivedCategory.Q :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.ε
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

/-- The actual coefficient-system unit, concentrated in cochain degree zero.
Its horizontal maps are the coefficient quotients because its underlying presheaf is
that of the sequence-site ring itself. Source: Stacks 07A4
(blueprint: lem-pur-normalized-operation-system-models). -/
def operationUnitComplex :=
  (CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj
    (SheafOfModules.unit (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing.{c,
      v, max c v r} J B τ)))

/-- The whole-system unit in the ordinary unbounded localization.
Source: Stacks 07A4 (blueprint: lem-pur-normalized-operation-system-models). -/
def operationUnit : DS.{c, v, max c v r} J B τ :=
  DerivedCategory.Q.obj (operationUnitComplex.{c, v, r} J B τ)

attribute [local irreducible] operationUnitComplex operationUnit

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors evaluation
  ordinaryTensorHom tensorSection

/-- The explicit law formula, named to keep structure projections compact.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-pur-normalized-operation-system-models). -/
def operationTensorPureFormula (A : Data.{c, v, r} J B τ) : Prop :=
  ∀ (M N : Systems.{c, v, max c v r} J B τ)
    (_hM : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ)
      ((CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj M))
    (_hN : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ)
      ((CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj N))
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (a : ((evaluation.{c, v, max c v r} J B τ m).obj M).val.obj U)
    (x : ((evaluation.{c, v, max c v r} J B τ m).obj N).val.obj U) (b : (B n).obj.obj U),
    ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U)
        ((ordinaryReduction.{c, v, r} J B τ A h
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r}
            J B τ) M N)).val.app U
          (b • scalarExtensionSection.{c, v, r} (coefficientMap.{c, v, max c v r} J B τ h)
            (A.scalar h)
            ((evaluation.{c, v, max c v r} J B τ m).obj
              (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v
                r} J B τ) M N)) U
            (((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U)
              (tensorSection.{c, v, r} J (B m) ((evaluation.{c, v, max c v r} J B τ m).obj M)
                ((evaluation.{c, v, max c v r} J B τ m).obj N) U a x)))) =
      tensorSection.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U
        (((SemilinearSections.transition J B τ h).app M).val.app U a)
        (b • @id (((evaluation.{c, v, max c v r} J B τ n).obj N).val.obj U)
          (((SemilinearSections.transition J B τ h).app N).val.app U x))

/-- The explicit law formula, named to keep structure projections compact.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-pur-normalized-operation-system-models). -/
def operationTensorCochainFormula (A : Data.{c, v, r} J B τ) : Prop :=
  ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    {m n : ℕ} (h : n ≤ m),
    (A.scalarTensorModel h).chain
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj P)
        (((evaluation.{c, v, max c v r} J B τ m).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
        h)).map
        ((A.tensorEvaluationModel m).chain P Q) ≫
      cochainReduction.{c, v, r} J B τ A h
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q)) =
    (totalTensor.{c, v, r} J (B n)).map
        (Prod.mkHom (cochainReduction.{c, v, r} J B τ A h P) (cochainReduction.{c, v, r} J B τ A h
          Q)) ≫
      (A.tensorEvaluationModel n).chain P Q

/-- Normalization, the actual tensor adjoint, and its quotient cocycle. These are
properties of the tensor of whole systems, with evaluations only in the comparison
square. Source: Stacks 07A4, 0D6D and 07A6
(blueprint: lem-pur-normalized-operation-system-models). -/
structure OperationTensorLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- Tensor preserves normalization. -/
  normalized : ∀ (M N : DS.{c, v, max c v r} J B τ),
    Normalized.{c, v, max c v r} J B τ A.scalar M → Normalized.{c, v, max c v r} J B τ A.scalar N →
      Normalized.{c, v, max c v r} J B τ A.scalar (A.closed.tensor.obj (M, N))
  /-- The adjoint of the actual tensor transition is monoidal scalar extension
  followed by the tensor of the two original adjoints. -/
  transition : ∀ (M N : DS.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m),
    reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (M, N)) ≫
        (A.tensorEvaluation n).hom.app (M, N) =
      (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (M, N)) ≫
        (A.scalarTensor h).hom.app ((e.{c, v, max c v r} J B τ m).obj M, (e.{c, v, max c v r} J B
          τ m).obj N) ≫
        (A.levelClosed n).tensor.map
          (Prod.mkHom (reduction.{c, v, max c v r} J B τ h (A.scalar h) M)
            (reduction.{c, v, max c v r} J B τ h (A.scalar h) N))
  /-- The actual input transition factors through its scalar-insertion unit. -/
  input_factor : ∀ (M : DS.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m),
    (derivedTransition.{c, v, max c v r} J B τ h).app M =
      (A.scalar h).adjunction.unit.app ((e.{c, v, max c v r} J B τ m).obj M) ≫
        (resD.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (reduction.{c, v,
          max c v r} J B τ h (A.scalar h) M)
  /-- Successive output adjoints equal the direct output adjoint. -/
  cocycle : ∀ (M N : DS.{c, v, max c v r} J B τ)
    {k m n : ℕ} (h : n ≤ m) (j : m ≤ k),
    (A.scalar h).T.map
        (reduction.{c, v, max c v r} J B τ j (A.scalar j) (A.closed.tensor.obj (M, N))) ≫
        reduction.{c, v, max c v r} J B τ h (A.scalar h) (A.closed.tensor.obj (M, N)) =
      (A.scalarComposition h j).hom.app
          ((e.{c, v, max c v r} J B τ k).obj (A.closed.tensor.obj (M, N))) ≫
        reduction.{c, v, max c v r} J B τ (h.trans j) (A.scalar (h.trans j)) (A.closed.tensor.obj
          (M, N))
  /-- On local flat representatives the scalar adjoint uses the actual transitions,
  sending (a tensor x) tensor b to tau(a) tensor b tau(x). -/
  pure : operationTensorPureFormula.{c, v, r} J B τ A
  /-- The same tensor adjoint equation holds on whole-system cochain maps,
  before localization and before evaluating a derived morphism. -/
  cochain : operationTensorCochainFormula.{c, v, r} J B τ A



/-- The explicit law formula, named to keep structure projections compact.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-pur-normalized-operation-system-models). -/
def operationModelQuotientFormula (A : Data.{c, v, r} J B τ) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (P : CochainComplex (Mod.{c, v, max c v r} J (B m)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B m) P →
    flatTerms.{c, v, r} J (B m) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
          h)).obj P) ∧
      flatTerms.{c, v, r} J (B n) ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max
        c v r} J B τ h) (A.scalar h)).obj P) ∧
      IsIso ((operationScalarCounit.{c, v, r} J
        (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)).app P)

/-- The resolution and closure formulation of simultaneous finite expression models.
A representative is chosen once on the sequence site. The closure clauses are for
arbitrary integer-indexed complexes, so structural induction gives every finite tensor
or coefficient-pullback expression without further replacements. All resulting chain
objects remain whole systems. Source: Stacks 06YS, 07A2, 07A4 and 0G7E
(blueprint: lem-pur-normalized-operation-system-models). -/
structure OperationModelLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- One whole-system resolution resolves all components simultaneously. -/
  resolution : ∀ K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    ∃ (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) (q : P ⟶ K),
      QuasiIso q ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P ∧
      ∀ n : ℕ,
        CochainComplex.IsKFlatIndependentCoefficients (R := B n)
          (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up
            ℤ)).obj P) ∧
        flatTerms.{c, v, r} J (B n) (((SemilinearSections.evaluation.{c, v, max c v r} J B τ
          n).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Every further model can still be evaluated without losing K-flatness or flat terms. -/
  evaluation : ∀ P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P →
    ∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
          (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} J (B n)
        (((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
          (.up ℤ)).obj P)
  /-- Total tensor preserves the chosen whole-system representative class. -/
  tensor : ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) Q →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) Q →
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ)
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q)) ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B
          τ)).obj (P, Q))
  /-- The same closure holds for evaluated tensor vertices. -/
  level_tensor : ∀ (n : ℕ) (P Q : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) Q →
    flatTerms.{c, v, r} J (B n) P → flatTerms.{c, v, r} J (B n) Q →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((totalTensor.{c, v, r} J (B n)).obj (P, Q)) ∧
      flatTerms.{c, v, r} J (B n) ((totalTensor.{c, v, r} J (B n)).obj (P, Q))
  /-- Coefficient quotients preserve K-flatness AND flat terms, and their actual
  universal derived counit computes them. There is no quotient-flatness hypothesis. -/
  quotient : operationModelQuotientFormula.{c, v, r} J B τ A


attribute [local semireducible] evaluation

/-- The unit is the coefficient system in degree zero, with quotient transitions,
whose adjoints are invertible multiplication maps. Source: Stacks 07A4 and 07A6
(blueprint: lem-pur-normalized-operation-system-models). -/
structure OperationUnitLaws (A : Data.{c, v, r} J B τ) : Prop where
  /-- The regular whole-system complex is K-flat. -/
  kflat : CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ)
    (operationUnitComplex.{c, v, r} J B τ)
  /-- Every term is flat. -/
  flat : flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
    (operationUnitComplex.{c, v, r} J B τ)
  /-- The quotient adjoints are isomorphisms. -/
  normalized : Normalized.{c, v, max c v r} J B τ A.scalar (operationUnit.{c, v, r} J B τ)
  /-- Before localization the quotient adjoint is an isomorphism of complexes. -/
  transition : ∀ {m n : ℕ} (h : n ≤ m),
    IsIso (cochainReduction.{c, v, r} J B τ A h (operationUnitComplex.{c, v, r} J B τ))

  /-- The unit adjoint is multiplication q(s)b on the regular module in degree zero. -/
  multiplication : ∀ {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (s : (B m).obj.obj U) (b : (B n).obj.obj U),
    (ordinaryReduction.{c, v, r} J B τ A h
        (SheafOfModules.unit (ring.{c, v, max c v r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)))).val.app U
      (b • scalarExtensionSection.{c, v, r}
        (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)
        ((SemilinearSections.evaluation.{c, v, max c v r} J B τ m).obj
          (SheafOfModules.unit (ring.{c, v, max c v r} (coefficientSequenceTopology J)
            (systemRing.{c, v, max c v r} J B τ)))) U s) =
      ((coefficientMap.{c, v, max c v r} J B τ h).hom.app U s) * b


section Geometric
variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
  (A : Data.{c, v, r} J B τ)
  (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)

/-- Actual geometric transition adjoints, scalar association and finite-model closure.
The inverse scalar association is fixed by its ordinary adjunction transpose, whose
unit inserts 1; its derived version is fixed by Geometry.coefficientPullback_transpose.
Source: Stacks 07A4, 0D6D, 0G7E and 07A6
(blueprint: lem-pur-normalized-operation-system-models). -/
structure OperationPullLaws : Prop where
  /-- Inverse image preserves normalization. -/
  normalized : ∀ M : DS.{c, v, max c v r} J B τ,
    Normalized.{c, v, max c v r} J B τ A.scalar M →
      Normalized.{c, v, max c v r} J' G.coefficients G.coefficientTransition G.target.scalar
        (G.pull.mapDerivedCategory.obj M)
  /-- The actual adjoint is kappa inverse followed by pullback of the input adjoint. -/
  transition : G.PullTransitionFormula J B τ A J' uInv uPush adjSet
  /-- Successive output adjoints equal the direct output adjoint. -/
  cocycle : ∀ (M : DS.{c, v, max c v r} J B τ)
    {k m n : ℕ} (h : n ≤ m) (j : m ≤ k),
    (G.target.scalar h).T.map
        (reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition j (G.target.scalar j)
          (G.pull.mapDerivedCategory.obj M)) ≫
        reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition h (G.target.scalar h)
          (G.pull.mapDerivedCategory.obj M) =
      (G.target.scalarComposition h j).hom.app
          ((e.{c, v, max c v r} J' G.coefficients G.coefficientTransition k).obj
            (G.pull.mapDerivedCategory.obj M)) ≫
        reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition (h.trans j)
          (G.target.scalar (h.trans j)) (G.pull.mapDerivedCategory.obj M)
  /-- Both paths of scalar association multiply the same three scalar factors. -/
  scalar_cocycle : ∀ {k m n : ℕ} (h : n ≤ m) (j : m ≤ k)
    (P : D.{c, v, max c v r} J (B k)),
    (derivedExact.{c, v, max c v r, c, v} J J' (B n) (G.coefficients n) (G.inverseImage
      n).modules).map
        ((A.scalarComposition h j).hom.app P) ≫
        (G.coefficientPullback (h.trans j)).hom.app P =
      (G.coefficientPullback h).hom.app ((A.scalar j).T.obj P) ≫
        (G.target.scalar h).T.map ((G.coefficientPullback j).hom.app P) ≫
        (G.target.scalarComposition h j).hom.app
          ((derivedExact.{c, v, max c v r, c, v} J J' (B k) (G.coefficients k) (G.inverseImage
            k).modules).obj P)
  /-- The ordinary association isomorphism, constructed before localization.
  Its inverse is uniquely characterized by the scalar-insertion unit. -/
  ordinary_scalar : ∃ κ : ∀ {m n : ℕ} (h : n ≤ m),
      operationScalarFunctor.{c, v, r} J
          (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h) ⋙
          (G.inverseImage n).modules ≅
        (G.inverseImage m).modules ⋙ operationScalarFunctor.{c, v, r} J'
          (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition h)
          (G.target.scalar h),
    (∀ {m n : ℕ} (h : n ≤ m) (P : Mod.{c, v, max c v r} J (B m)),
      ((G.target.scalar h).ordinaryAdjunction.homEquiv _ _) ((κ h).inv.app P) =
        (G.inverseImage m).modules.map ((A.scalar h).ordinaryAdjunction.unit.app P) ≫
          (G.restrictionPullback h).hom.app
            ((operationScalarFunctor.{c, v, r} J
              (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)).obj P)) ∧
    (∀ {m n : ℕ} (h : n ≤ m) (M : Systems.{c, v, max c v r} J B τ),
      ordinaryReduction.{c, v, r} J' G.coefficients G.coefficientTransition G.target h
          (G.pull.obj M) ≫ (G.ordinaryPullEvaluation n).hom.app M =
        (operationScalarFunctor.{c, v, r} J'
            (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition h)
            (G.target.scalar h)).map ((G.ordinaryPullEvaluation m).hom.app M) ≫
          (κ h).inv.app ((evaluation.{c, v, max c v r} J B τ m).obj M) ≫
          (G.inverseImage n).modules.map (ordinaryReduction.{c, v, r} J B τ A h M))
  /-- Termwise geometric pullback preserves the whole-system representative class. -/
  whole_model : ∀ P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) P →
    flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) P →
    CochainComplex.IsKFlatIndependentCoefficients
        (R := systemRing.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
        ((G.pull.mapHomologicalComplex (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
        ((G.pull.mapHomologicalComplex (.up ℤ)).obj P)
  /-- Evaluated geometric pullback also preserves K-flatness and flat terms.
  Its exact derived functor and canonical localization comparison compute it. -/
  level_model : ∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B n) P →
    flatTerms.{c, v, r} J (B n) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := G.coefficients n)
        (((G.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} J' (G.coefficients n)
        (((G.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P)
end Geometric


attribute [local semireducible] operationUnitComplex operationUnit
  SheafOfModules.monoidalCategory

attribute [local irreducible] evaluation

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSection_smul (R : Sheaf J CommRingCat.{max c v r})
    (M N : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (b : R.obj.obj U) :
    tensorSection.{c, v, r} J R M N U x (b • y) =
      b • tensorSection.{c, v, r} J R M N U x y := by
  let : HasSheafify J AddCommGrpCat.{max c v r} := abelianSheafify J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let a : M.val ⊗ N.val ⟶ (ordinaryTensor.{c, v, r} J R M N).val :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ring.{c, v, max c v r} J R).obj)).unit.app (M.val ⊗ N.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M N).inv.val
  unfold tensorSection
  change (a.app U) (x ⊗ₜ (b • y)) = b • (a.app U) (x ⊗ₜ y)
  change (a.app U) (TensorProduct.tmul (R.obj.obj U) x (b • y)) =
    b • (a.app U) (TensorProduct.tmul (R.obj.obj U) x y)
  erw [TensorProduct.tmul_smul (R := R.obj.obj U) (R' := R.obj.obj U)]
  exact (a.app U).hom.map_smul b (x ⊗ₜ y)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_tensor_laws (A : Data.{c, v, r} J B τ) :
    OperationTensorLaws.{c, v, r} J B τ A := by
  have ht := tensor_reduction_formula.{c, v, r} J B τ A
  refine {
    normalized := ?_
    transition := ht
    input_factor := ?_
    cocycle := by
      intro M N k m n h j
      exact A.reduction_cocycle h j (A.closed.tensor.obj (M, N))
    pure := ?_
    cochain := by
      intro P Q m n h
      exact cochain_tensor_reduction.{c, v, r} J B τ A h P Q
  }
  · intro M N hM hN m n h
    have h₁ := hM h
    have h₂ := hN h
    have : IsIso (Prod.mkHom
        (reduction.{c, v, max c v r} J B τ h (A.scalar h) M)
        (reduction.{c, v, max c v r} J B τ h (A.scalar h) N)) :=
      (asIso (reduction.{c, v, max c v r} J B τ h (A.scalar h) M) |>.prod
        (asIso (reduction.{c, v, max c v r} J B τ h (A.scalar h) N))).isIso_hom
    have hi : IsIso
        (reduction.{c, v, max c v r} J B τ h (A.scalar h)
          (A.closed.tensor.obj (M, N)) ≫ (A.tensorEvaluation n).hom.app (M, N)) := by
      rw [ht M N h]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hi
  · intro M m n h
    simpa only [reduction, Equiv.apply_symm_apply] using
      ((A.scalar h).adjunction.homEquiv_unit _ _
        (reduction.{c, v, max c v r} J B τ h (A.scalar h) M))
  · intro M N _ _ m n h U a x b
    let z := (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
      (tensorSection.{c, v, r} J (B m) _ _ U a x)
    have hh := congrArg ((A.scalar h).ordinaryAdjunction.homEquiv _ _)
      (ordinary_tensor_reduction.{c, v, r} J B τ A h M N)
    rw [(A.scalar h).ordinaryAdjunction.homEquiv_naturality_right,
      (A.scalar h).ordinaryAdjunction.homEquiv_naturality_left] at hh
    simp only [ordinaryReduction, Equiv.apply_symm_apply] at hh
    have hs := congrArg (fun f ↦ f.val.app U z) hh
    change (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
        (((SemilinearSections.transition J B τ h).app _).val.app U z) =
      (((A.scalar h).ordinaryAdjunction.homEquiv _ _)
        (((A.scalarTensorModel h).ordinary _ _).hom ≫
          ordinaryTensorHom.{c, v, r} J (B n)
            (ordinaryReduction.{c, v, r} J B τ A h M)
            (ordinaryReduction.{c, v, r} J B τ A h N))).val.app U
        ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).hom.val.app U z) at hs
    have hz : (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).hom.val.app U z =
        tensorSection.{c, v, r} J (B m) _ _ U a x := by
      change (((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv ≫
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).hom).val.app U) _ = _
      rw [Iso.inv_hom_id]
      rfl
    rw [hz, scalar_tensor_transpose_section.{c, v, r} J
      (coefficientMap J B τ h) (A.scalar h) (A.scalarTensorModel h).ordinary
      (A.scalarTensorModel h).ordinary_pure] at hs
    simp only [ordinaryReduction, Equiv.apply_symm_apply] at hs
    have hu := transpose_section.{c, v, r} J (coefficientMap J B τ h)
      (A.scalar h)
      ((evaluation.{c, v, max c v r} J B τ m).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N))
      ((evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N)) (ordinaryReduction.{c, v, r} J B τ A h
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N)) U z
    simp only [ordinaryReduction, Equiv.apply_symm_apply] at hu
    change _ = tensorSection.{c, v, r} J (B n) _ _ U _ (b • _)
    rw [map_smul, map_smul]
    change b • (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
      ((ordinaryReduction.{c, v, r} J B τ A h _).val.app U
        (scalarExtensionSection.{c, v, r} (coefficientMap J B τ h)
          (A.scalar h) _ U z)) = _
    simp only [ordinaryReduction]
    have heq := (congrArg
      ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U) hu.symm).trans hs
    refine (congrArg (fun y ↦ b • y) heq).trans ?_
    exact (tensorSection_smul.{c, v, r} J (B n) _ _ U _ _ b).symm



set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_model_laws (A : Data.{c, v, r} J B τ) :
    OperationModelLaws.{c, v, r} J B τ A := by
  have he (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := systemRing.{c, v, max c v r} J B τ) P)
      (hf : flatTerms.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) P) (n : ℕ) :=
    And.intro ((A.tensorEvaluationModel n).kflat P hP hf)
      (show flatTerms.{c, v, r} J (B n)
        (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
        from fun i ↦ evaluation_preserves_flat.{c, v, r} J B τ n (P.X i) (hf i))
  refine {
    resolution := ?_
    evaluation := he
    tensor := ?_
    level_tensor := ?_
    quotient := ?_
  }
  · intro K
    obtain ⟨P, q, hP, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v r, c, v}
        (R := systemRing.{c, v, max c v r} J B τ) K
    have hf' : flatTerms.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) P := fun i ↦
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (systemRing.{c, v, max c v r} J B τ) (P.X i)).symm (hf i)
    exact ⟨P, q, hq, hP, hf', he P hP hf'⟩
  · intro P Q hP hQ hfP hfQ
    have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      (systemRing.{c, v, max c v r} J B τ) P Q hP hQ hfP hfQ
    exact ⟨h.1, h.2.1⟩
  · intro n P Q hP hQ hfP hfQ
    have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      (B n) P Q hP hQ hfP hfQ
    exact ⟨h.1, h.2.1⟩
  · intro m n h P hP hf
    have hf' (i : ℤ) : exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory (B m))
          (P.X i)) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (B m) (P.X i)) (hf i)
    have hc := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (coefficientMap.{c, v, max c v r} J B τ h) P
      (A.scalar h).model.E (A.scalar h).model.obj_eq (A.scalar h).model.map_eq hP hf'
    refine ⟨hc.1, ?_, (A.scalar h).model.computes P hP⟩
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (B n) _).symm (hc.2 i)


set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_unit_flat :
    flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) (operationUnitComplex.{c, v, r} J B τ) := by
  let R := systemRing.{c, v, max c v r} J B τ
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let A := Systems.{c, v, max c v r} J B τ
  have hunit : SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := coefficientSequenceTopology J) (R := R) (SheafOfModules.unit (ring _ R)) := by
    have hf : exactFunctor A A (MonoidalCategory.tensorRight (𝟙_ A)) :=
      (exactFunctor A A).prop_of_iso (MonoidalCategory.rightUnitorNatIso A).symm
        ⟨inferInstanceAs (PreservesFiniteLimits (𝟭 A)),
          inferInstanceAs (PreservesFiniteColimits (𝟭 A))⟩
    exact (exactFunctor A A).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hf
  intro i
  by_cases hi : i = 0
  · subst i
    exact hunit
  · have hz : IsZero ((operationUnitComplex.{c, v, r} J B τ).X i) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
    have hcat : ObjectProperty.flat ((operationUnitComplex.{c, v, r} J B τ).X i) :=
      ObjectProperty.flat.prop_of_isZero hz
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hcat.2

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_unit_kflat :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := systemRing.{c, v, max c v r} J B τ)
      (operationUnitComplex.{c, v, r} J B τ) := by
  let P := operationUnitComplex.{c, v, r} J B τ
  have : P.IsStrictlyLE (0 : ℤ) := by
    dsimp only [P, operationUnitComplex]
    infer_instance
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (systemRing.{c, v, max c v r} J B τ) P 0 (operation_unit_flat.{c, v, r} J B τ)

attribute [local semireducible] evaluation

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def evaluationUnitIso (n : ℕ) :
    (evaluation.{c, v, max c v r} J B τ n).obj
        (SheafOfModules.unit (ring (coefficientSequenceTopology J) (systemRing J B τ))) ≅
      SheafOfModules.unit (ring J (B n)) := by
  let R := ring.{c, v, max c v r} J (B n)
  let M := SheafOfModules.unit
    (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing J B τ))
  let e (U : Cᵒᵖ) : ((evaluation J B τ n).obj M).val.obj U ≃ₗ[R.obj.obj U]
      (SheafOfModules.unit R).val.obj U :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ evaluation_smul.{c, v, r} J B τ n M U a x }
  exact (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (e U).toModuleIso) (by
      intro U V f
      ext x
      exact evaluation_ring_map.{c, v, r} J B τ n f x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem transition_unit_apply {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (s : (B m).obj.obj U) :
    ((transition.{c, v, max c v r} J B τ h).app
      (SheafOfModules.unit (ring (coefficientSequenceTopology J) (systemRing J B τ)))).val.app U
      s = (coefficientMap J B τ h).hom.app U s := by
  let M := SheafOfModules.unit
    (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing J B τ))
  have hh := transition_apply_cast.{c, v, r} J B τ h M U s
  simp only [evalSection, cast_eq] at hh
  rw [hh]
  change (ringPresheaf.{c, v, max c v r} J B τ).map
    (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op s = _
  unfold ringPresheaf
  rw [horizontal_map']
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_unit_multiplication (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (s : (B m).obj.obj U) (b : (B n).obj.obj U) :
    (ordinaryReduction.{c, v, r} J B τ A h
      (SheafOfModules.unit (ring (coefficientSequenceTopology J) (systemRing J B τ)))).val.app U
      (b • scalarExtensionSection.{c, v, r} (coefficientMap J B τ h) (A.scalar h)
        ((evaluation.{c, v, max c v r} J B τ m).obj
          (SheafOfModules.unit (ring (coefficientSequenceTopology J) (systemRing J B τ))))
        U s) = (coefficientMap J B τ h).hom.app U s * b := by
  rw [map_smul]
  let M := SheafOfModules.unit
    (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing J B τ))
  have ht := transpose_section.{c, v, r} J (coefficientMap J B τ h) (A.scalar h)
    ((evaluation.{c, v, max c v r} J B τ m).obj M)
    ((evaluation.{c, v, max c v r} J B τ n).obj M)
    (ordinaryReduction.{c, v, r} J B τ A h M) U s
  simp only [ordinaryReduction, Equiv.apply_symm_apply] at ht
  have he : (ordinaryReduction.{c, v, r} J B τ A h M).val.app U
      (scalarExtensionSection.{c, v, r} (coefficientMap J B τ h) (A.scalar h)
        ((evaluation.{c, v, max c v r} J B τ m).obj M) U s) =
      (coefficientMap J B τ h).hom.app U s :=
    ht.symm.trans (transition_unit_apply.{c, v, r} J B τ h U s)
  refine (congrArg (fun x ↦ b • x) he).trans ?_
  exact (evaluation_smul.{c, v, r} J B τ n M U b
    ((coefficientMap J B τ h).hom.app U s)).trans (by
      change b * _ = _ * b
      exact mul_comm _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_unit_ordinary_iso (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) :
    IsIso (ordinaryReduction.{c, v, r} J B τ A h
      (SheafOfModules.unit (ring (coefficientSequenceTopology J) (systemRing J B τ)))) := by
  let M := SheafOfModules.unit
    (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing J B τ))
  let p := evaluationUnitIso.{c, v, r} J B τ m
  let q := evaluationUnitIso.{c, v, r} J B τ n
  apply isIso_of_coyoneda_map_bijective
  intro N
  let resN := (res (coefficientMap J B τ h)).obj N
  let e : (((evaluation J B τ n).obj M) ⟶ N) ≃
      ((A.scalar h).model.E.obj ((evaluation J B τ m).obj M) ⟶ N) :=
    (Iso.homCongr q (Iso.refl N)) |>.trans (SheafOfModules.unitHomEquiv N)
      |>.trans (SheafOfModules.unitHomEquiv resN).symm
      |>.trans (Iso.homCongr p.symm (Iso.refl resN))
      |>.trans ((A.scalar h).ordinaryAdjunction.homEquiv _ _).symm
  have he (f : (evaluation J B τ n).obj M ⟶ N) :
      e f = ordinaryReduction.{c, v, r} J B τ A h M ≫ f := by
    apply ((A.scalar h).ordinaryAdjunction.homEquiv _ _).injective
    dsimp only [e, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply]
    change p.hom ≫ (SheafOfModules.unitHomEquiv resN).symm
      (SheafOfModules.unitHomEquiv N (q.inv ≫ f)) = _
    rw [(A.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
    simp only [ordinaryReduction, Equiv.apply_symm_apply]
    apply (cancel_epi p.inv).mp
    simp only [Iso.inv_hom_id_assoc]
    apply (SheafOfModules.unitHomEquiv resN).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    funext U
    change f.val.app U (1 : (B n).obj.obj U) =
      f.val.app U (((transition J B τ h).app M).val.app U (1 : (B m).obj.obj U))
    rw [transition_unit_apply.{c, v, r} J B τ h,
      ((coefficientMap J B τ h).hom.app U).hom.map_one]
  have hh : (fun f ↦ ordinaryReduction.{c, v, r} J B τ A h M ≫ f) = e :=
    funext fun f ↦ (he f).symm
  rw [hh]
  exact e.bijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_unit_transition (A : Data.{c, v, r} J B τ)
    {m n : ℕ} (h : n ≤ m) :
    IsIso (cochainReduction.{c, v, r} J B τ A h
      (operationUnitComplex.{c, v, r} J B τ)) := by
  have : ∀ i : ℤ, IsIso ((cochainReduction.{c, v, r} J B τ A h
      (operationUnitComplex.{c, v, r} J B τ)).f i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact operation_unit_ordinary_iso.{c, v, r} J B τ A h
    · have hz : IsZero ((operationUnitComplex.{c, v, r} J B τ).X i) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      exact IsZero.isIso
        ((A.scalar h).model.E.map_isZero
          ((evaluation.{c, v, max c v r} J B τ m).map_isZero hz))
        ((evaluation.{c, v, max c v r} J B τ n).map_isZero hz) _
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_unit_laws (A : Data.{c, v, r} J B τ) :
    OperationUnitLaws.{c, v, r} J B τ A := by
  refine {
    kflat := operation_unit_kflat.{c, v, r} J B τ
    flat := operation_unit_flat.{c, v, r} J B τ
    normalized := ?_
    transition := operation_unit_transition.{c, v, r} J B τ A
    multiplication := operation_unit_multiplication.{c, v, r} J B τ A
  }
  intro m n h
  let P := operationUnitComplex.{c, v, r} J B τ
  have hP := (operation_model_laws.{c, v, r} J B τ A).evaluation P
    (operation_unit_kflat.{c, v, r} J B τ) (operation_unit_flat.{c, v, r} J B τ) m
  have hf := reduction_on_kflat_evaluation.{c, v, r} J B τ A h P hP.1
  rw [← cochainReduction_eq_transpose] at hf
  have := operation_unit_transition.{c, v, r} J B τ A h
  have := (A.scalar h).model.computes _ hP.1
  have hi : IsIso
      (reduction.{c, v, max c v r} J B τ h (A.scalar h) (DerivedCategory.Q.obj P) ≫
        (Functor.mapDerivedCategoryFactors (evaluation J B τ n)).hom.app P) := by
    rw [hf]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

attribute [local irreducible] evaluation evaluationCoefficientEquiv evaluationSectionEquiv

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem flat_of_evaluation (M : Systems.{c, v, max c v r} J B τ)
    (hf : ∀ n : ℕ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)) :
    SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) M := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion
    (systemRing.{c, v, max c v r} J B τ) M
  rintro ⟨n, U⟩ t a s hs
  have hs' : ∑ i, (evaluationCoefficientEquiv.{c, v, r} J B τ n (op U)).symm (a i) •
      (evaluationSectionEquiv.{c, v, r} J B τ n M (op U)).symm (s i) = 0 := by
    apply (evaluationSectionEquiv.{c, v, r} J B τ n M (op U)).injective
    simpa only [map_sum, map_zero, evaluationSectionEquiv_smul.{c, v, r} J B τ n,
      AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] using hs
  obtain ⟨S, hS, h⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite
      (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M) (hf n) U t
      (fun i ↦ (evaluationCoefficientEquiv.{c, v, r} J B τ n (op U)).symm (a i))
      (fun i ↦ (evaluationSectionEquiv.{c, v, r} J B τ n M (op U)).symm (s i)) hs'
  let T : Sieve (n, U) :=
    { arrows := fun Y f ↦ S f.2
      downward_closed := by
        intro Y Z f hf g
        exact S.downward_closed hf g.2 }
  refine ⟨T, hS, ?_⟩
  rintro ⟨m, V⟩ f hf
  obtain ⟨l, b, z, hz, hb⟩ := h V f.2 hf
  let b₀ := fun i j ↦ evaluationCoefficientEquiv.{c, v, r} J B τ n (op V) (b i j)
  let z₀ := fun j ↦ evaluationSectionEquiv.{c, v, r} J B τ n M (op V) (z j)
  have hz₀ (i : Fin t) : M.val.map ((Prod.sectR n C).map f.2).op (s i) =
      ∑ j, b₀ i j • z₀ j := by
    have hi := congrArg (evaluationSectionEquiv.{c, v, r} J B τ n M (op V)) (hz i)
    simp only [map_sum, evaluationSectionEquiv_smul.{c, v, r} J B τ n,
      evaluationSectionEquiv_map.{c, v, r} J B τ n M,
      AddEquiv.apply_symm_apply] at hi
    convert hi using 1 <;> rfl
  let R := (systemRing.{c, v, max c v r} J B τ).obj
  have hb₀ (j : Fin l) : ∑ i, (show (systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, V)) from
        R.map ((Prod.sectR n C).map f.2).op (a i)) * b₀ i j = 0 := by
    have hj := congrArg (evaluationCoefficientEquiv.{c, v, r} J B τ n (op V)) (hb j)
    simp only [map_sum, map_mul, map_zero,
      evaluationCoefficientEquiv_map.{c, v, r} J B τ n,
      RingEquiv.apply_symm_apply] at hj
    convert hj using 1
    rfl
  let k : (m, V) ⟶ (n, V) := Prod.mkHom f.1 (𝟙 V)
  refine ⟨l, (fun i j ↦ R.map k.op (b₀ i j)),
    (fun j ↦ M.val.map k.op (z₀ j)), ?_, ?_⟩
  · intro i
    have hi := congrArg (fun x ↦ M.val.map k.op x) (hz₀ i)
    simp only [map_sum] at hi
    have hsm (j : Fin l) := M.val.map_smul k.op (b₀ i j) (z₀ j)
    have hi' : M.val.map k.op (M.val.map ((Prod.sectR n C).map f.2).op (s i)) =
        ∑ j, (show M.val.obj (op (m, V)) from
          (R.map k.op (b₀ i j)) • (show M.val.obj (op (m, V)) from M.val.map k.op (z₀ j))) := by
      refine hi.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
      convert hsm j using 1 <;> rfl
    change M.val.map f.op (s i) = _
    rw [show f = k ≫ (Prod.sectR n C).map f.2 by ext <;> simp [k]]
    erw [op_comp, M.val.map_comp_apply]
    exact hi'
  · intro j
    have hj := congrArg (fun x ↦ R.map k.op x) (hb₀ j)
    simp only [map_sum, map_mul, map_zero] at hj
    change ∑ i, R.map f.op (a i) * R.map k.op (b₀ i j) = 0
    rw [show f = k ≫ (Prod.sectR n C).map f.2 by ext <;> simp [k]]
    refine Eq.trans ?_ hj
    apply Finset.sum_congr rfl
    intro i hi
    erw [op_comp, R.map_comp]
    rfl

section PullProof
variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (A : Data.{c, v, r} J B τ)
  (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_level_adjunction_underlying (n : ℕ)
    (M : Mod.{c, v, max c v r} J (B n))
    (N : Mod.{c, v, max c v r} J' (G.coefficients n))
    (f : (G.inverseImage n).modules.obj M ⟶ N) :
    (underlying.{c, v, r} J (B n)).map
        ((G.levelAdjunction n).homEquiv M N f) ≫
      (G.levelPushUnderlying n).hom.app N =
    adjSet.homEquiv _ _ ((G.inverseImage n).moduleUnderlying.inv.app M ≫
      (underlying.{c, v, r} J' (G.coefficients n)).map f) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (G.levelPushUnderlying n).hom.naturality f
  change (underlying.{c, v, r} J (B n)).map ((G.levelPush n).map f) ≫
      (G.levelPushUnderlying n).hom.app N =
    (G.levelPushUnderlying n).hom.app ((G.inverseImage n).modules.obj M) ≫
      uPush.map ((underlying.{c, v, r} J' (G.coefficients n)).map f) at hn
  rw [Category.assoc, hn]
  change _ = _ ≫ uPush.map _
  rw [← G.level_unit_underlying n M, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_restriction_mate_underlying {m n : ℕ} (h : n ≤ m)
    (N : Mod.{c, v, max c v r} J' (G.coefficients n)) :
    (underlying.{c, v, r} J (B m)).map
        ((mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
          (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).app N) ≫
      (G.levelPushUnderlying m).hom.app
        ((res (coefficientMap J' G.coefficients G.coefficientTransition h)).obj N) =
      (G.levelPushUnderlying n).hom.app N := by
  let q := res (coefficientMap J' G.coefficients G.coefficientTransition h)
  let p := res (coefficientMap J B τ h)
  let f := (G.restrictionPullback h).hom.app ((G.levelPush n).obj N) ≫
    q.map ((G.levelAdjunction n).counit.app N)
  have hm : (G.levelAdjunction m).homEquiv _ _ f =
      (mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
        (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).app N := by
    apply ((G.levelAdjunction m).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit (G.levelAdjunction n) (G.levelAdjunction m)
      (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom) N).symm
  rw [← hm]
  erw [operation_level_adjunction_underlying.{c, v, r} J B τ J' uInv uPush adjSet A G m _ _ f]
  have hf : (G.inverseImage m).moduleUnderlying.inv.app
      (p.obj ((G.levelPush n).obj N)) ≫
      (underlying.{c, v, r} J' (G.coefficients m)).map f =
    (G.inverseImage n).moduleUnderlying.inv.app ((G.levelPush n).obj N) ≫
      (underlying.{c, v, r} J' (G.coefficients n)).map
        ((G.levelAdjunction n).counit.app N) := by
    have hr := G.restrictionPullback_underlying h ((G.levelPush n).obj N)
    have hr' : (underlying.{c, v, r} J' (G.coefficients m)).map
        ((G.restrictionPullback h).hom.app ((G.levelPush n).obj N)) =
      (G.inverseImage m).moduleUnderlying.hom.app (p.obj ((G.levelPush n).obj N)) ≫
        (G.inverseImage n).moduleUnderlying.inv.app ((G.levelPush n).obj N) := by
      apply (cancel_mono ((G.inverseImage n).moduleUnderlying.hom.app _)).mp
      erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      exact hr
    dsimp only [f]
    rw [Functor.map_comp, hr']
    erw [← Category.assoc, Iso.inv_hom_id_app_assoc]
    rfl
  refine (congrArg (adjSet.homEquiv _ _) hf).trans ?_
  refine (operation_level_adjunction_underlying.{c, v, r} J B τ J' uInv uPush adjSet A G n
    ((G.levelPush n).obj N) N ((G.levelAdjunction n).counit.app N)).symm.trans ?_
  rw [← (G.levelAdjunction n).homEquiv_symm_id, Equiv.apply_symm_apply]
  rw [(underlying.{c, v, r} J (B n)).map_id]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_ordinary_association_iso {m n : ℕ} (h : n ≤ m) :
    IsIso ((mateEquiv (A.scalar h).ordinaryAdjunction
      (G.target.scalar h).ordinaryAdjunction).symm
        (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).natTrans := by
  let δ := (mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
    (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).natTrans
  have hδ (N : Mod.{c, v, max c v r} J' (G.coefficients n)) : IsIso (δ.app N) := by
    have he := operation_restriction_mate_underlying.{c, v, r} J B τ J' uInv uPush adjSet A G h N
    have hi : IsIso ((underlying.{c, v, r} J (B m)).map (δ.app N) ≫
        (G.levelPushUnderlying m).hom.app
          ((res (coefficientMap J' G.coefficients G.coefficientTransition h)).obj N)) := by
      rw [he]
      exact (inferInstance : IsIso ((G.levelPushUnderlying n).hom.app N))
    have : IsIso ((underlying.{c, v, r} J (B m)).map (δ.app N)) :=
      IsIso.of_isIso_comp_right _ ((G.levelPushUnderlying m).hom.app _)
    exact isIso_of_reflects_iso _ (underlying.{c, v, r} J (B m))
  have : IsIso δ := NatIso.isIso_of_isIso_app _
  let a := (A.scalar h).ordinaryAdjunction.comp (G.levelAdjunction n)
  let b := (G.levelAdjunction m).comp (G.target.scalar h).ordinaryAdjunction
  have he := iterated_mateEquiv_conjugateEquiv_symm
    (A.scalar h).ordinaryAdjunction (G.target.scalar h).ordinaryAdjunction
    (G.levelAdjunction m) (G.levelAdjunction n)
    (mateEquiv (G.levelAdjunction n) (G.levelAdjunction m)
      (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom))
  have hβ : IsIso ((conjugateEquiv a b).symm δ) := by infer_instance
  have he' := congrArg TwoSquare.natTrans he
  simp only [Equiv.symm_apply_apply, Equiv.trans_apply] at he'
  rw [he']
  exact hβ

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_ordinary_scalar : ∃ κ : ∀ {m n : ℕ} (h : n ≤ m),
      operationScalarFunctor.{c, v, r} J
          (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h) ⋙
          (G.inverseImage n).modules ≅
        (G.inverseImage m).modules ⋙ operationScalarFunctor.{c, v, r} J'
          (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition h)
          (G.target.scalar h),
    (∀ {m n : ℕ} (h : n ≤ m) (P : Mod.{c, v, max c v r} J (B m)),
      ((G.target.scalar h).ordinaryAdjunction.homEquiv _ _) ((κ h).inv.app P) =
        (G.inverseImage m).modules.map ((A.scalar h).ordinaryAdjunction.unit.app P) ≫
          (G.restrictionPullback h).hom.app
            ((operationScalarFunctor.{c, v, r} J
              (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)).obj P)) ∧
    (∀ {m n : ℕ} (h : n ≤ m) (M : Systems.{c, v, max c v r} J B τ),
      ordinaryReduction.{c, v, r} J' G.coefficients G.coefficientTransition G.target h
          (G.pull.obj M) ≫ (G.ordinaryPullEvaluation n).hom.app M =
        (operationScalarFunctor.{c, v, r} J'
            (coefficientMap.{c, v, max c v r} J' G.coefficients G.coefficientTransition h)
            (G.target.scalar h)).map ((G.ordinaryPullEvaluation m).hom.app M) ≫
          (κ h).inv.app ((evaluation.{c, v, max c v r} J B τ m).obj M) ≫
          (G.inverseImage n).modules.map (ordinaryReduction.{c, v, r} J B τ A h M)) := by
  let β {m n : ℕ} (h : n ≤ m) :
      (G.inverseImage m).modules ⋙ operationScalarFunctor.{c, v, r} J'
          (coefficientMap J' G.coefficients G.coefficientTransition h) (G.target.scalar h) ⟶
        operationScalarFunctor.{c, v, r} J (coefficientMap J B τ h) (A.scalar h) ⋙
          (G.inverseImage n).modules :=
    ((mateEquiv (A.scalar h).ordinaryAdjunction
      (G.target.scalar h).ordinaryAdjunction).symm
        (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom)).natTrans
  have hi {m n : ℕ} (h : n ≤ m) : IsIso (β h) :=
    operation_ordinary_association_iso.{c, v, r} J B τ J' uInv uPush adjSet A G h
  let κ {m n : ℕ} (h : n ≤ m) := (asIso (β h)).symm
  have hb {m n : ℕ} (h : n ≤ m) (P : Mod.{c, v, max c v r} J (B m)) :
      ((G.target.scalar h).ordinaryAdjunction.homEquiv _ _) ((κ h).inv.app P) =
        (G.inverseImage m).modules.map ((A.scalar h).ordinaryAdjunction.unit.app P) ≫
          (G.restrictionPullback h).hom.app
            ((operationScalarFunctor.{c, v, r} J (coefficientMap J B τ h) (A.scalar h)).obj P) := by
    exact (unit_mateEquiv_symm (A.scalar h).ordinaryAdjunction
      (G.target.scalar h).ordinaryAdjunction
      (TwoSquare.mk _ _ _ _ (G.restrictionPullback h).hom) P).symm
  refine ⟨κ, hb, ?_⟩
  intro m n h M
  dsimp only [operationScalarFunctor]
  apply ((G.target.scalar h).ordinaryAdjunction.homEquiv _ _).injective
  rw [(G.target.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
  simp only [ordinaryReduction, Equiv.apply_symm_apply]
  rw [(G.target.scalar h).ordinaryAdjunction.homEquiv_naturality_left,
    (G.target.scalar h).ordinaryAdjunction.homEquiv_naturality_right]
  dsimp only [Functor.comp_obj]
  have hbm := hb h ((evaluation.{c, v, max c v r} J B τ m).obj M)
  dsimp only [Functor.comp_obj, operationScalarFunctor] at hbm
  erw [hbm]
  have hn := (G.restrictionPullback h).hom.naturality
    (ordinaryReduction.{c, v, r} J B τ A h M)
  dsimp only [Functor.comp_map, ordinaryReduction] at hn
  simp only [Category.assoc]
  rw [← hn, ← (G.inverseImage m).modules.map_comp_assoc]
  have hu := (A.scalar h).ordinaryAdjunction.homEquiv_unit _ _
    (ordinaryReduction.{c, v, r} J B τ A h M)
  simp only [ordinaryReduction, Equiv.apply_symm_apply] at hu
  rw [← hu]
  exact G.ordinaryPullTransition h M

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_pull_normalized
    (ht : G.PullTransitionFormula J B τ A J' uInv uPush adjSet)
    (M : DS.{c, v, max c v r} J B τ)
    (hM : Normalized.{c, v, max c v r} J B τ A.scalar M) :
    Normalized.{c, v, max c v r} J' G.coefficients G.coefficientTransition G.target.scalar
      (G.pull.mapDerivedCategory.obj M) := by
  intro m n h
  have := hM h
  have hi : IsIso
      (reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition h
        (G.target.scalar h) (G.pull.mapDerivedCategory.obj M) ≫
        (G.pullEvaluation n).hom.app M) := by
    rw [ht h M]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

variable [PreservesFiniteLimits uInv]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_pull_level_model (n : ℕ)
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B n) P)
    (hf : flatTerms.{c, v, r} J (B n) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := G.coefficients n)
        (((G.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} J' (G.coefficients n)
        (((G.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine ⟨(G.levelTensorModel n).kflat P hP hf, ?_⟩
  intro i
  let : HasSheafify J AddCommGrpCat.{max c v r} := abelianSheafify J
  let : HasSheafify J' AddCommGrpCat.{max c v r} := abelianSheafify J'
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J
  let : J'.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J'
  exact SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{c, v, c, v, max c v r, max c v r}
    uInv uPush adjSet
    (SheafOfModules.inverseImageOfUniverses.{c, v, c, v, max c v r} (G.inverseImage n))
    (P.X i) (hf i)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem operation_pull_whole_model
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := systemRing.{c, v, max c v r} J B τ) P)
    (hf : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P) :
    CochainComplex.IsKFlatIndependentCoefficients
        (R := systemRing.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
        ((G.pull.mapHomologicalComplex (.up ℤ)).obj P) ∧
      flatTerms.{c, v, r} (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' G.coefficients G.coefficientTransition)
        ((G.pull.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine ⟨G.tensorModel.kflat P hP hf, ?_⟩
  intro i
  apply flat_of_evaluation.{c, v, r} J' G.coefficients G.coefficientTransition
  intro n
  have hi :=
    SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{c, v, c, v, max c v r, max c v r}
    uInv uPush adjSet
    (SheafOfModules.inverseImageOfUniverses.{c, v, c, v, max c v r} (G.inverseImage n))
    ((evaluation.{c, v, max c v r} J B τ n).obj (P.X i))
    (evaluation_preserves_flat.{c, v, r} J B τ n (P.X i) (hf i))
  exact SheafOfModules.flatOnSite_of_iso (G.coefficients n)
    ((G.ordinaryPullEvaluation n).app (P.X i)).symm hi
end PullProof

end WeilConjectures.SemilinearSections

attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.NormalizedOperations
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The constant-section coefficient map, with no equality of coefficient and site
universes. This is the sheafification extension of the same constant-section map
used in the recorded pro-etale coefficient structure morphism.
Source: Stacks 00YV, 09A5 (blueprint: lem-pur-normalized-operation-system-models). -/
def coefficientDirect {X : Scheme.{t}} (f : X ⟶ W) (n : ℕ) :
    integralCoefficientCommRingSheaf l E W n ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology W)
          (Scheme.ProEt.topology X)).obj (integralCoefficientCommRingSheaf l E X n) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology W)
    CommRingCat.{max u (t + 1)}).homEquiv _ _).symm
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))))

/-- The geometric model uses exactly the finite coefficient sheaves on X. The
underlying inverse-image ring comparison is the transpose of the canonical
constant-section map, so an arbitrary identification cannot be substituted.
Source: Stacks 00YV, 07A4 (blueprint: lem-pur-normalized-operation-system-models). -/
def CoefficientsIdentified (A : Calculus l E W) {X : Scheme.{t}} (f : X ⟶ W)
    (G : Geometry.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      A.systems (Scheme.ProEt.topology X) (inverse.{t, u} f) (direct.{t, u} f)
      (geometricAdjunction.{t, u} f)) : Prop :=
  ∃ h : G.coefficients = integralCoefficientCommRingSheaf l E X,
    (∀ n : ℕ, HEq (G.coefficientTransition n) (coefficientSequenceCommRingTransition l E X n)) ∧
    ∀ n : ℕ,
      ((geometricAdjunction.{t, u} f).homEquiv _ _)
        ((G.inverseImage n).ringUnderlying.hom ≫
          (sheafCompose (Scheme.ProEt.topology X)
            (CategoryTheory.forget CommRingCat.{max u (t + 1)})).map
              (eqToHom (congrFun h n))) =
        (sheafCompose (Scheme.ProEt.topology W)
          (CategoryTheory.forget CommRingCat.{max u (t + 1)})).map
            (coefficientDirect l E W f n)

/-- All clauses of normalized finite coefficient-system operations. The three
model closure clauses and geometric model closure give every finite well-typed
iteration by structural induction, retaining the original whole-system transitions.
Source: Stacks 07A4, 0D6D, 06YS, 07A2, 0G7E and 07A6
(blueprint: lem-pur-normalized-operation-system-models). -/
def HasOperationSystemModels (A : Calculus l E W) : Prop :=
  OperationTensorLaws.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      A.systems ∧
  OperationUnitLaws.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      A.systems ∧
  OperationModelLaws.{t + 1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      A.systems ∧
  ∀ (X : Scheme.{t}) (f : X ⟶ W) (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)),
    ∃ G : Geometry.{t + 1, t, u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        A.systems (Scheme.ProEt.topology X) (inverse.{t, u} f) (direct.{t, u} f)
        (geometricAdjunction.{t, u} f),
      CoefficientsIdentified l E W A f G ∧
      OperationPullLaws.{t + 1, t, u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (Scheme.ProEt.topology X) (inverse.{t, u} f) (direct.{t, u} f)
        (geometricAdjunction.{t, u} f) A.systems G ∧
      OperationTensorLaws.{t + 1, t, u} (Scheme.ProEt.topology X)
        G.coefficients G.coefficientTransition G.target ∧
      OperationUnitLaws.{t + 1, t, u} (Scheme.ProEt.topology X)
        G.coefficients G.coefficientTransition G.target ∧
      OperationModelLaws.{t + 1, t, u} (Scheme.ProEt.topology X)
        G.coefficients G.coefficientTransition G.target

/-- Tensor, geometric inverse image, and the unit preserve normalization with the
specified actual transition adjoints, coherent scalar association, and simultaneous
flat-term K-flat models for every finite iteration.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0D6D, together with
06YS, 07A2, 0G7E and 07A6 (blueprint: lem-pur-normalized-operation-system-models).

Proof:
1. The supplied tensor-reduction formula factors the actual reduction through the
   two input reductions and monoidal scalar extension. All these factors are
   invertible on normalized inputs. Scalar transposition and tensor linearity give
   the section formula; the supplied chain reduction and cocycle give coherence.
2. Resolve once on the sequence site. The supplied evaluation model preserves
   K-flatness, and evaluation preserves flat terms. Total tensor and scalar
   change-of-rings preserve these models, including nonflat coefficient quotients.
3. The regular sequence-site module is flat, and its degree-zero single complex
   is K-flat. Evaluation identifies it with the regular coefficient module. The
   ordinary unit reduction is invertible because precomposition with it is the
   equivalence of sections supplied by the scalar adjunction. The representative
   counit comparison proves normalization of its derived reduction.
4. Realize geometric systems on the literal canonical coefficient tower using
   canonicalCoefficientSystemGeometry. Its actual pull-transition formula
   preserves normalization. The target reduction cocycle is supplied by its Data;
   geometricScalarAssociationCocycle proves scalar coherence by localizing the
   ordinary restriction square and transposing its composition equation.
5. The ordinary scalar comparison is the mate of restrictionPullback. Its further
   level-adjunction mate has identity underlying map by the normalized unit and
   underlying-sheaf equations, hence is invertible. The iterated-mate identity
   proves the scalar mate invertible. Hom-equivalence naturality gives its unit
   formula and the actual transition formula.
6. The supplied geometric models preserve K-flatness. Level algebraic inverse
   image preserves flat terms. To recover whole-system flatness, use the local
   finite-relation criterion at level n, lift its covering sieve to the sequence
   site, and restrict the factorization witnesses horizontally to every m over n.
   Semilinearity preserves both matrix equations. These closure clauses give every
   finite iteration while retaining all original whole-system transitions.
-/
theorem normalizedOperationSystemModels
    (_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w)) (A : Calculus l E W) :
    HasOperationSystemModels l E W A := by
  refine ⟨operation_tensor_laws.{t + 1, t, u} _ _ _ A.systems,
    operation_unit_laws.{t + 1, t, u} _ _ _ A.systems,
    operation_model_laws.{t + 1, t, u} _ _ _ A.systems, ?_⟩
  intro X f _hX
  let : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : AB5OfSize.{t, t + 1} (Type (max u (t + 1))) :=
    AB5OfSize_shrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  let : PreservesFiniteLimits
      ((Scheme.proEtaleBaseChange f).op.lan :
        (W.ProEtᵒᵖ ⥤ Type (max u (t + 1))) ⥤ X.ProEtᵒᵖ ⥤ Type (max u (t + 1))) :=
    preservesFiniteLimits_op_lan_of_flat _
  let : PreservesFiniteLimits (inverse.{t, u} f) :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
      (Scheme.proEtaleBaseChange f) (Type (max u (t + 1)))
      (Scheme.ProEt.topology W) (Scheme.ProEt.topology X)
  obtain ⟨G, hcoeff, hpull⟩ := canonicalCoefficientSystemGeometry l E W A X f
  refine ⟨G, hcoeff, ?_, operation_tensor_laws.{t + 1, t, u} _ _ _ G.target,
    operation_unit_laws.{t + 1, t, u} _ _ _ G.target,
    operation_model_laws.{t + 1, t, u} _ _ _ G.target⟩
  refine {
    normalized := operation_pull_normalized.{t + 1, t, u} _ _ _ _ _ _ _ A.systems G hpull
    transition := hpull
    cocycle := by
      intro M k m n h j
      exact G.target.reduction_cocycle h j _
    scalar_cocycle := geometricScalarAssociationCocycle.{t + 1, t, u} _ _ _ _ _ _ _ A.systems G
    ordinary_scalar := operation_ordinary_scalar.{t + 1, t, u} _ _ _ _ _ _ _ A.systems G
    whole_model := operation_pull_whole_model.{t + 1, t, u} _ _ _ _ _ _ _ A.systems G
    level_model := operation_pull_level_model.{t + 1, t, u} _ _ _ _ _ _ _ A.systems G
  }

end WeilConjectures.NormalizedOperations
