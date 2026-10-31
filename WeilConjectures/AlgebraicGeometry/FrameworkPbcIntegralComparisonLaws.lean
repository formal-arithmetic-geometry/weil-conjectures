/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrameworkPbcComparisonSystem

/-! # Normalized integral framework/PBC comparison laws

Source: current blueprint, purity-transport coefficient-change argument.
(blueprint: lem-pur-framework-pbc-integral-comparison-laws).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc

/-- The integral portion of the framework/PBC bridge for a prescribed simultaneous
strict-system realization. No rational coefficient equivalence or raw comparison is
asserted here.
Source: current blueprint, smooth-purity/purity-transport coefficient-change argument,
Steps 1--7 of lem-pur-framework-pbc-pullback-scalar-bridge; Stacks 099N, 0941,
07A4 and 0D6D
(blueprint: lem-pur-framework-pbc-integral-comparison-laws).

Proof: Relabel coefficients with the completed-presentation equivalence, retaining
all quotient projections and structural maps. Adic presentation transport identifies
ordinary pullbacks and their whole quotient towers, with their counits. Exact
countable products and the strict Roos comparison identify the two realizations;
the quotient augmentation and zero shifted coordinate give the required Pullback
normalization. Resolution independence descends this to constructible objects.
For the prescribed realization, tower substitution retains the iterated counits.
The finite compositors agree on balanced tensors. Completion-unit uniqueness fixes
the PBC compositor, giving the unit and composition equations without transporting
an arbitrarily chosen compositor along pi.
Finite freeness identifies ordinary scalar extension with the completed model.
Use inverse chi followed by coefficient relabeling for the specified scalarComponent.
The unit-preserving completion comparison identifies inverse completed balancing
with completion of inverse ordinary balancing followed by kappa. Both scalar-square
routes agree on every generator of the whole strict tower, so realization gives
the stated equation. Relabel signed total tensors in both Roos coordinates to obtain
tau. The ordinary scalar tensor map sends s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y); completion gives ScalarTensor.completed and the
tensor square. Identity and successive extensions give multiplication and tensor
associativity on the same systems, proving the scalar unit and tower equations.
All these degree-zero maps preserve the signed differentials, quotient augmentations,
and both Roos coordinates, so the specified comparisons descend with the displayed
integer-shift equations. None of these steps assumes flatness of ramified quotient
maps or geometric exchange invertibility. -/
theorem frameworkPbcIntegralComparisonLaws
    (l : ℕ) [Fact l.Prime] (realization : IntegralComparisonSystem.{u} l)
    (realization_coherent : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B),
      IntegralComparisonRealizationCoherence l A B i realization)
 :
    ∃ pullback : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))],
      (h : X ⟶ Y) → Pullback l A h,
    ∃ scalar : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Scalar l A B i W,
    ∃ tensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Tensor l A W,
    ∃ scalarTensor : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
      [IsNoetherian W] [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
      ScalarTensor l A B i W,
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
      (K : sfIntegralConstructibleCategory l A W),
      (pullback A (𝟙 W)).pi.hom.app K ≫
        (pbcActualCompletedPullIdIso (pbcIntegralDatum l A) W).hom.app
          ⟨(integralDetailedTransport W l A).obj K.obj,
            (purDetailedTransport_complete_iff l A W K.obj).mp K.property.1⟩ =
        (integralDetailedTransport W l A).map
          (integralComparisonUnit l A realization W K).hom) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X Y Z : Scheme.{u})
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
      [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
      (h : X ⟶ Y) (g : Y ⟶ Z) (K : sfIntegralConstructibleCategory l A Z),
      (pullback A (h ≫ g)).pi.hom.app K ≫
        (pbcActualCompletedPullCompIso h g (pbcIntegralDatum l A)).inv.app
          ⟨(integralDetailedTransport Z l A).obj K.obj,
            (purDetailedTransport_complete_iff l A Z K.obj).mp K.property.1⟩ =
      (integralDetailedTransport X l A).map
          (integralComparisonComposition l A realization h g K).hom ≫
        (pullback A h).pi.hom.app ((constructibleIntegralPullback l A g).obj K) ≫
        (pbcActualCompletedPull h (pbcIntegralDatum l A)).map
          ((pullback A g).pi.hom.app K)) ∧
    (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B)
      {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
      (h : X ⟶ Y) (K : sfIntegralConstructibleCategory l A Y),
      (integralDetailedTransport X l B).map
          (integralPullbackScalarComparison l A B i h K).hom.hom ≫
        (pullback B h).pi.hom.app ((integralComparisonConstructibleScalar l A B i Y).obj K) ≫
        (pbcActualCompletedPull h (pbcIntegralDatum l B)).map
          (scalarComponent l A B i Y K).hom =
      (scalarComponent l A B i X ((constructibleIntegralPullback l A h).obj K)).hom ≫
        (pbcEmbeddingAmbientTensor l A B i X).map ((pullback A h).pi.hom.app K) ≫
        (pbcScalarCompletedPullIso l A B i h).inv.app
          ((integralDetailedTransport Y l A).obj K.obj)) ∧
    (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B)
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
      (M N : sfIntegralConstructibleCategory l A W),
      (pbcEmbeddingAmbientTensor l A B i W).map ((tensor A W).tau.inv.app (M.obj, N.obj)) ≫
        (scalarComponent l A B i W ((constructibleIntegralTensor l A W).obj (M, N))).inv ≫
        (integralDetailedTransport W l B).map
          (integralTensorScalarComparison l A B i W M N).hom.hom ≫
        (tensor B W).tau.hom.app
          (((integralComparisonConstructibleScalar l A B i W).obj M).obj,
            ((integralComparisonConstructibleScalar l A B i W).obj N).obj) ≫
        (FrameworkPbc.tensor l B W).map
          (Prod.mkHom (scalarComponent l A B i W M).hom
            (scalarComponent l A B i W N).hom) =
      ((scalarTensor A B i W).completed l A B i).hom.app
        ((integralDetailedTransport W l A).obj M.obj,
          (integralDetailedTransport W l A).obj N.obj)) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
      (K : sfIntegralConstructibleCategory l A W),
      (scalarComponent l A A (AlgHom.id ℚ_[l] A) W K).hom ≫
        (pbcEmbeddingAmbientUnit l A W).hom.app
          ((integralDetailedTransport W l A).obj K.obj) =
      (integralDetailedTransport W l A).map (integralComparisonScalarUnit l A W K).hom) ∧
    (∀ (A B C : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] [Field C] [Algebra ℚ_[l] C]
      [FiniteDimensional ℚ_[l] C] (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C)
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
      (K : sfIntegralConstructibleCategory l A W),
      (scalarComponent l B C j W ((integralComparisonConstructibleScalar l A B i W).obj K)).hom ≫
        (pbcEmbeddingAmbientTensor l B C j W).map (scalarComponent l A B i W K).hom ≫
        (pbcAmbientScalarComp l A B C i j W).hom.app
          ((integralDetailedTransport W l A).obj K.obj) =
      (integralDetailedTransport W l C).map
          (integralComparisonScalarAssociator l A B i C j W K).hom ≫
        (scalarComponent l A C (j.comp i) W K).hom) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] (h : X ⟶ Y),
      ∃ c : (integralOperationsPullbackComplexFunctor l A h).CommShift ℤ,
      ∃ d : (integralDerivedPullback l A h).CommShift ℤ,
        IntegralCompletedComparison.ShiftCoordinates l A h c ∧
        IntegralCompletedComparison.ShiftDescent l A h c d ∧
        ∀ (K : sfIntegralConstructibleCategory l A Y) (r : ℤ),
        ∃ hKr : sfIntegralConstructible l A Y (K.obj⟦r⟧),
        HEq ((integralDetailedTransport X l A).map
            ((Functor.commShiftIso (integralDerivedPullback l A h) (self := d) r).hom.app
              K.obj) ≫
          ((fdCoefficientTransport l A X).mapDerivedCategory.commShiftIso r).hom.app
            ((integralDerivedPullback l A h).obj K.obj) ≫
          ((pullback A h).pi.hom.app K)⟦r⟧')
          ((pullback A h).pi.hom.app ⟨K.obj⟦r⟧, hKr⟩ ≫
            (pbcActualCompletedPull h (pbcIntegralDatum l A)).map
              (((fdCoefficientTransport l A Y).mapDerivedCategory.commShiftIso r).hom.app
                K.obj) ≫
            ((pbcActualCompletedPull h (pbcIntegralDatum l A)).commShiftIso r).hom.app
              ((integralDetailedTransport Y l A).obj K.obj))) ∧
    (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
      [IsNoetherian W] [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
      ∃ (c : (integralScalarComplexFunctor l A B i W).CommShift ℤ)
        (o : (completedDerivedScalarExtension l A B i W).CommShift ℤ)
        (d : (integralScalarExtension l A B i W).CommShift ℤ),
        completedScalarShiftRepresentativeProperty i W c o d ∧
        ∀ (K : sfIntegralConstructibleCategory l A W) (r : ℤ),
        ∃ hKr : sfIntegralConstructible l A W (K.obj⟦r⟧),
        HEq ((integralDetailedTransport W l B).map
            ((Functor.commShiftIso (integralScalarExtension l A B i W) (self := d) r).hom.app
              K.obj) ≫
          ((fdCoefficientTransport l B W).mapDerivedCategory.commShiftIso r).hom.app
            ((integralScalarExtension l A B i W).obj K.obj) ≫
          (scalarComponent l A B i W K).hom⟦r⟧')
          ((scalarComponent l A B i W ⟨K.obj⟦r⟧, hKr⟩).hom ≫
            (pbcEmbeddingAmbientTensor l A B i W).map
              (((fdCoefficientTransport l A W).mapDerivedCategory.commShiftIso r).hom.app
                K.obj) ≫
            ((pbcEmbeddingAmbientTensor l A B i W).commShiftIso r).hom.app
              ((integralDetailedTransport W l A).obj K.obj))) := by sorry

end WeilConjectures.FrameworkPbc
