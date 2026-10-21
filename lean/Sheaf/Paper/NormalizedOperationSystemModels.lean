/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SystemCochainTensorReduction
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.CategoryTheory.SystemEvaluationKFlat
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

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
universe t u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
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
abbrev operationScalarFunctor {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} J S :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.E
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

/-- Termwise extension with its recorded additive witness made explicit.
Source: Stacks 06YY (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev operationScalarComplex {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :=
  letI : (operationScalarFunctor.{c, v, r} J φ A).Additive :=
    @SheafOfModules.DerivedChangeOfRingsCochainModel.additive
      C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
      (abelianSheafify.{c, v, max c v r} J) R S φ
      (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model
  (operationScalarFunctor.{c, v, r} J φ A).mapHomologicalComplex (.up ℤ)

/-- The actual universal derived counit of scalar extension, at the chosen sizes.
Source: Stacks 06YY (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev operationScalarCounit {R S : Sheaf J CommRingCat.{max c v r}}
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
abbrev operationUnitComplex :=
  (CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj
    (SheafOfModules.unit (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing.{c,
      v, max c v r} J B τ)))

/-- The whole-system unit in the ordinary unbounded localization.
Source: Stacks 07A4 (blueprint: lem-pur-normalized-operation-system-models). -/
abbrev operationUnit : DS.{c, v, max c v r} J B τ :=
  DerivedCategory.Q.obj (operationUnitComplex.{c, v, r} J B τ)

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
  pure : ∀ (M N : Systems.{c, v, max c v r} J B τ)
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
  /-- The same tensor adjoint equation holds on whole-system cochain maps,
  before localization and before evaluating a derived morphism. -/
  cochain : ∀ (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
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
  quotient : ∀ {m n : ℕ} (h : n ≤ m) (P : CochainComplex (Mod.{c, v, max c v r} J (B m)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := B m) P →
    flatTerms.{c, v, r} J (B m) P →
    CochainComplex.IsKFlatIndependentCoefficients (R := B n)
        ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar
          h)).obj P) ∧
      flatTerms.{c, v, r} J (B n) ((operationScalarComplex.{c, v, r} J (coefficientMap.{c, v, max
        c v r} J B τ h) (A.scalar h)).obj P) ∧
      IsIso ((operationScalarCounit.{c, v, r} J
        (coefficientMap.{c, v, max c v r} J B τ h) (A.scalar h)).app P)

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
end WeilConjectures.SemilinearSections

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
1. Resolve a complex on the ringed sequence site using lem-pc-kflat-resolution.
   Evaluation preserves flat-term K-flat models by lem-pur-system-evaluation-kflat.
   This is one resolution of systems, retaining all horizontal maps and cocycles.
2. Induct on the finite expression. Tensor vertices use lem-pur-kflat-total-tensor-model;
   pullback vertices, including nonflat coefficient quotients, use
   lem-weil-pbc-ringed-pullback-preserves-kflat. The universal representative comparisons
   in lem-coef-semilinear-derived-sections and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback compute the derived operations.
3. The actual tensor transition is tau(a) tensor tau(x). Its scalar adjoint sends
   (a tensor x) tensor b to tau(a) tensor b tau(x), by
   lem-pur-sheaf-ring-derived-coefficient-adjunction. Factor it through monoidal
   scalar extension from lem-pur-cochain-pullback-tensor-coherence and the two input
   adjoints. The factors are invertible on normalized inputs.
4. The constant-section ring maps are invertible by
   prop-weil-pbc-proetale-constant-ring-map. Their quotient square commutes on
   constants, hence on sheafifications. Scalar association sends
   b tensor (p tensor a) to (1 tensor p) tensor b c(a). Its inverse sends
   (s tensor p) tensor b to b q(s) tensor (p tensor 1). Balancing proves the inverse
   identities; the ordinary transpose in OperationPullLaws fixes this insertion of 1.
5. The actual pulled transition has adjunct (s tensor p) tensor b mapped to
   b q(s) tensor tau(p). Thus it is kappa inverse followed by pullback of the original
   adjunct, not a replacement of tau by the scalar unit. It is invertible for a
   normalized input.
6. For three indices, both tensor paths give tau(a) tensor q(b)c tau(x). Both pullback
   paths give c q(b)q(s) tensor tau(p). Input cocycles and associativity prove the
   equations on system chain maps before localization. Equal indices give identities.
7. The whole unit is the regular sequence-site module concentrated in degree zero.
   Its adjunct s tensor b mapped to q(s)b is an isomorphism with inverse b mapped to
   1 tensor b. It is flat-term K-flat and supplies the unit base case of the induction.
   No boundedness or flatness of a quotient homomorphism is used.
-/
theorem normalizedOperationSystemModels
    (_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w)) (A : Calculus l E W) :
    HasOperationSystemModels l E W A := by
  sorry

end WeilConjectures.NormalizedOperations
