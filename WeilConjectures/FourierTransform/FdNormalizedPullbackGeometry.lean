/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
public import WeilConjectures.FourierTransform.FdPullbackAugmentationCounitMatching
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Geometric coherence of the fixed normalized pullback components

Source: trace-definition auxiliary whole-tower argument, as recorded in the parent
comparison node; Stacks 0941 and 099N
(blueprint: lem-fd-normalized-pullback-geometry). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The fixed augmentation-normalized finite comparisons obey the actual unit,
composition and signed shift equations, for one realization system.
Source: trace-definition auxiliary whole-tower argument, steps 6--7 and 11;
Stacks 099N, 0D6D and 014E
(blueprint: lem-fd-normalized-pullback-geometry).

Proof: compare each finite component to the ambient comparison in
fdCompletedCompositorNormalization. Both composites with the inverse-image
augmentation are the actual completed-pullback unit, by FdPullbackRoosMatching
and the quotient/zero-coordinate normalization of FdPullbackComparison.
The augmentation is invertible on complete constructible objects, so these
ambient components agree. Fullness and the lift field give the same equality
for the integral components. Restrict integralComparisonUnit and
integralComparisonComposition to the full constructible categories and restrict
the actual PBC identity and inverse compositor. Their inverse maps and naturality
restrict as well. Substitution in the two normalized equations gives precisely
the unit and composition formulas below, in the inverse-b orientation.
For shifts, fdPullbackSignedShiftWordTransport supplies the signed cone shift
and its descent. Its primitive ambient comparison has the same normalized
augmentation, so the preceding uniqueness identifies it with the selected
component. Transfer its shift square and invert the comparison. Constructibility
is preserved under shifts, giving hKr. The sign acts only on the shifted cone
coordinate and fixes the augmentation (0,z), also for negative integers and r=0.
All cancellations take place on complete inputs, never on arbitrary ambient
completion units. Identity scheme maps and zero objects use these same equations. -/
theorem fdNormalizedPullbackGeometry (R : IntegralComparisonSystem.{u} l)
    (C : ∀ (T : Scheme.{u}) [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))],
      FdCoefficientComparison l Ω T)
    (P : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
      [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
      (h : U ≅ T), FdPullbackSystem l Ω (C U) (C T) h)
    (_matching : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
      [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
      [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
      [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
      [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
      (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
      FdPullbackRoosMatching l Ω (C U) (C T) h E R ((P h).finite E)) :
    (∀ (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω),
    ∃ su : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (𝟙 T) ≅ 𝟭 _,
    ∃ pu : fdPbcIntegralPull l Ω (𝟙 T) E ≅ 𝟭 _,
      (∀ K, (su.hom.app K).hom =
        (integralComparisonUnit l (pbcFiniteField.{u} l Ω E) R T K).hom) ∧
      (∀ K, HEq (pu.hom.app K).hom
        ((pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Ω E) T).hom.app
          ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((P (Iso.refl T)).finite E).integral.hom.app K ≫
          ((C T).stage E).integral.functor.map (su.hom.app K) =
        pu.hom.app (((C T).stage E).integral.functor.obj K))) ∧
    (∀ (U V T : Scheme.{u})
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∀ t : V, IsUnit (l : V.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ V) (k : V ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
    ∃ sc : constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) (h.hom ≫ k.hom) ≅
        constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k.hom ⋙
          constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h.hom,
    ∃ pc : fdPbcIntegralPull l Ω (h.hom ≫ k.hom) E ≅
        fdPbcIntegralPull l Ω k.hom E ⋙ fdPbcIntegralPull l Ω h.hom E,
      (∀ K, (sc.hom.app K).hom =
        (integralComparisonComposition l (pbcFiniteField.{u} l Ω E) R
          h.hom k.hom K).hom) ∧
      (∀ K, HEq (pc.hom.app K).hom
        ((pbcActualCompletedPullCompIso h.hom k.hom
          (pbcStageDatum.{u} l Ω E)).inv.app ⟨K.obj, K.property.1⟩)) ∧
      (∀ K, ((P (h ≪≫ k)).finite E).integral.hom.app K ≫
          ((C U).stage E).integral.functor.map (sc.hom.app K) =
        pc.hom.app (((C T).stage E).integral.functor.obj K) ≫
          (fdPbcIntegralPull l Ω h.hom E).map
            (((P k).finite E).integral.hom.app K) ≫
          ((P h).finite E).integral.hom.app
            ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k.hom).obj K))) ∧
    (∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
    letI : (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).CommShift ℤ :=
      inferInstanceAs
        ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) U).mapDerivedCategory.CommShift ℤ)
    letI : (integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).CommShift ℤ :=
      inferInstanceAs
        ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapDerivedCategory.CommShift ℤ)
    ∃ c : (integralOperationsPullbackComplexFunctor l
      (pbcFiniteField.{u} l Ω E) h.hom).CommShift ℤ,
    ∃ d : (integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom).CommShift ℤ,
      IntegralCompletedComparison.ShiftCoordinates l (pbcFiniteField.{u} l Ω E) h.hom c ∧
      IntegralCompletedComparison.ShiftDescent l (pbcFiniteField.{u} l Ω E) h.hom c d ∧
      (fun [_sd : (integralDerivedPullback l
          (pbcFiniteField.{u} l Ω E) h.hom).CommShift ℤ] ↦
        ∀ (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) (r : ℤ),
        ∃ hKr : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T (K.obj⟦r⟧),
        HEq
          (((P h).finite E).ambient.hom.app ⟨K.obj⟦r⟧, hKr⟩ ≫
            ((integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom ⋙
              integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).commShiftIso
                r).hom.app K.obj)
          (((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
              pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E)).commShiftIso
                r).hom.app K.obj ≫
            (((P h).finite E).ambient.hom.app K)⟦r⟧')) (_sd := d)) := by sorry

end WeilConjectures
