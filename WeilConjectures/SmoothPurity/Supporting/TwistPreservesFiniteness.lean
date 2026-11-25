/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeSignedLineFiniteness
import Mathlib.Tactic.CongrExclamation

import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.Supporting.FieldTwistInverse
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.SmoothPurity.Integral.IntegralLineTensorCompleteness
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Tate twists preserve finiteness conditions

## Main definitions
* `TwistReductionMaps`
* `IsCanonicalTwistReductionMaps`

## Main statements
* `AlgebraicGeometry.ProEtale.twist_preserves_native_finiteness`: the current condensed statement.
* `twist_preserves_finiteness`: the retained legacy compatibility theorem.

## Implementation details

The current primary attachment uses ordinary unbounded derived tensor over the
actual pulled-back condensed coefficient rings. The completed/rationalized API
below remains for its existing callers. There, the intrinsic names `sfIntegralConstructible`,
`IsSfDerivedComplete` and `scalarReductionDerivedExtension` give the completed-coefficient
objects, canonical augmented Roos triangles and positive reductions; rational tensor and
common-stage tensor use the recorded intrinsic categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
local instance (priority := 10000) (Y : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} Y.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- The quotient unit in the prescribed first finite line, using the original
constant-integer tensor construction. -/
def twistFiniteFirstReductionSection (n : ℕ) (U : S.ProEtᵒᵖ)
    (x : (purTwistIntegralModule S l E).val.obj U) :
    (purTwistFiniteOne S l E n).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E S n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient S l E n) (purTwistIntegralOne S l E))).app U)
      ((1 : (integralCoefficientSheaf l E S n).obj.obj U) ⊗ₜ[
        (purTwistIntegralConstant S l E).obj.obj U,
        ((purTwistIntegralQuotient S l E n).hom.app U).hom] x)

/-- Semilinear reductions of all signed completed lines along the actual limit projection. -/
abbrev TwistReductionMaps (n : ℕ) := ∀ m : ℤ,
  integralTwistLine l E S m ⟶
    (scalarReductionRestriction l E S n).obj (finiteCoefficientTwist l E S n m)

/-- The reduction is fixed at zero by the coefficient projection, at one by the
original quotient tensor, at positive powers by tensoring, and at negative powers
by the dual evaluation pairing. -/
def IsCanonicalTwistReductionMaps (n : ℕ) (c : TwistReductionMaps l E S n) : Prop :=
  (∀ (U : S.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U),
    (c 0).val.app U a = (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (x : (purTwistIntegralModule S l E).val.obj U),
    (c 1).val.app U x = twistFiniteFirstReductionSection l E S n U x) ∧
  (∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U)
      (y : (purTwistIntegralModule S l E).val.obj U),
    (c (Int.ofNat (k + 2))).val.app U
      (SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := integralCoefficientCommRingSheaf l E S n) _ _ U
        ((c (Int.ofNat (k + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (k : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine l E S (Int.negSucc k)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted l E S)
        (purTwistIntegralModule S l E) (k + 1)).val.obj U),
    (((c (Int.negSucc k)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
      ((c (Int.ofNat (k + 1))).val.app U x) =
      (completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

private noncomputable def constantModulePullbackFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) := by
  have := constantComparison_isIso f A
  exact proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))

private theorem locallyConstant_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheaf Y A F) :
    IsLocallyConstantProEtaleModuleSheaf Y A G := by
  obtain ⟨I, U, f, hc, ht⟩ := hF
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  obtain ⟨M, ⟨hM⟩⟩ := ht i
  exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e.symm ≪≫ hM⟩⟩

private theorem finite_stalk_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    [Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)] :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) G) := by
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      ModuleCat.{u + 1} (proEtaleGeometricStalkRing y (proEtaleConstantRing Y A)) :=
    (SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y) _ ⋙
    PresheafOfModules.colimitFunctor (C := ProEtaleGeometricNeighbourhood y)
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y (proEtaleConstantRing Y A))))
  have : Finite (E.obj F) :=
    ‹Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)›
  change Finite (E.obj G)
  exact Finite.of_injective (E.mapIso e.symm).toLinearEquiv
    (E.mapIso e.symm).toLinearEquiv.injective

private theorem constructibleProEtale_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' : proEtaleConstantModulePullback (S.immersion i) A F ≅
      proEtaleConstantModulePullback (S.immersion i) A G :=
    (constantModulePullbackFunctor (S.immersion i) A).mapIso e
  refine ⟨locallyConstant_of_iso _ A e' (hS i).1, ?_⟩
  intro Ω _ _ y
  have := (hS i).2 Ω y
  exact finite_stalk_of_iso _ A e' y

private theorem exact_support_subset (A : Type u) [CommRing A]
    (F : proEtaleRingModules S (proEtaleConstantRing S A) ⥤
      proEtaleRingModules S (proEtaleConstantRing S A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : proEtaleDerivedCategory S A) :
    proEtaleCohomologicalSupport (F.mapDerivedCategory.obj K) ⊆
      proEtaleCohomologicalSupport K := by
  intro i hi hz
  exact hi (((F.mapDerivedCategoryHomologyFunctorIso i).app K).isZero_iff.mp
    (F.map_isZero hz))

private theorem support_iso (A : Type u) [CommRing A]
    {K K' : proEtaleDerivedCategory S A} (e : K ≅ K') :
    proEtaleCohomologicalSupport K = proEtaleCohomologicalSupport K' := by
  ext i
  exact not_congr ((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff

private theorem tor_of_iso (A : Type u) [CommRing A]
    {K K' : proEtaleDerivedCategory S A} (e : K ≅ K') (a b : ℤ)
    (h : HasProEtaleTorAmplitude S A K a b) : HasProEtaleTorAmplitude S A K' a b := by
  refine ⟨h.1, ?_⟩
  intro L P hL f hf hP M i hi
  exact h.2 L P (hL.map (fun e' ↦ e' ≪≫ e.symm)) f hf hP M i hi

omit [∀ x : S, Invertible (l : S.residueField x)] in
private theorem intrinsic_of_iso (n : ℕ)
    {K K' : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ K') (h : intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_pos n) S K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S K' := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  refine ⟨?_, fun i ↦ constructibleProEtale_of_iso S _
    ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.2 i)⟩
  change (proEtaleCohomologicalSupport K').Finite
  rw [← support_iso S _ e]
  exact h.1

private theorem finite_twist_constructible (n : ℕ) (m : ℤ)
    (hr : (finiteCoefficientTwist l E S n m).IsFiniteLocallyFreeOfRank 1)
    (K : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S
      ((finiteComplexTwist l E S n m).obj K) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let := hr
  let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
  let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
  let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
  let F := SheafOfModules.siteSheafTensorRight
    (A := integralCoefficientCommRingSheaf l E S n) (finiteCoefficientTwist l E S n m)
  refine ⟨hK.1.subset (exact_support_subset S _ F K), ?_⟩
  intro i
  exact constructibleProEtale_of_iso S _
    ((F.mapDerivedCategoryHomologyFunctorIso i).app K)
    ((finiteLineTensor_conditions S _ (finiteCoefficientTwist l E S n m)).2.1 _ (hK.2 i))

/-- The exact preservation and inverse-twist assertions at all four coefficients: the signed
twist lines are locally free of rank one with canonical reductions, and twisting by them
preserves finite-torsion constructibility, finite Tor amplitude, cohomological and Tor
intervals, derived completeness and integral constructibility, with inverse twists at the
finite, integral, rational and algebraically closed coefficients. -/
theorem twist_preserves_finiteness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    ∀ m : ℤ,
      (∀ n : ℕ,
        (finiteCoefficientTwist l E S n m).IsFiniteLocallyFreeOfRank 1 ∧
        IsLocallyConstantProEtaleModuleSheaf S (Padic.coefficientExtensionRing l E (n + 1))
          (finiteCoefficientTwist l E S n m)) ∧
      (integralTwistLine l E S m).IsFiniteLocallyFreeOfRank 1 ∧
      (∀ n : ℕ, ∃! c : TwistReductionMaps l E S n,
        IsCanonicalTwistReductionMaps l E S n c ∧
        ∀ k : ℤ, ∃! α : (scalarReductionExtension l E S n).obj
            (integralTwistLine l E S k) ≅ finiteCoefficientTwist l E S n k,
          ∀ (U : S.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
              (x : (integralTwistLine l E S k).val.obj U),
            α.hom.val.app U (sfReductionTensor l E S n (integralTwistLine l E S k) U a x) =
              a • (@id ((finiteCoefficientTwist l E S n k).val.obj U) ((c k).val.app U x))) ∧
      (∀ k : ℤ, ∀ n : ℕ, Nonempty ((scalarReductionDerivedExtension l E S n).obj
        (sfIntegralTwistingObject l E S k) ≅
          (DerivedCategory.singleFunctor _ 0).obj (finiteCoefficientTwist l E S n k))) ∧
      (∀ (n : ℕ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S K →
        intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) S
          ((finiteComplexTwist l E S n m).obj K)) ∧
      (∀ (n : ℕ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        finiteTorConstructible l E (n + 1) (Nat.succ_pos n) S K →
        finiteTorConstructible l E (n + 1) (Nat.succ_pos n) S
          ((finiteComplexTwist l E S n m).obj K)) ∧
      (∀ (n : ℕ) (a b : ℤ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        proEtaleCohomologicalSupport K ⊆ Set.Icc a b →
        proEtaleCohomologicalSupport ((finiteComplexTwist l E S n m).obj K) ⊆ Set.Icc a b) ∧
      (∀ (n : ℕ) (a b : ℤ) (K : proEtaleDerivedCategory S
          (Padic.coefficientExtensionRing l E (n + 1))),
        HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1)) K a b →
        HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
          ((finiteComplexTwist l E S n m).obj K) a b) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E S),
        sfIntegralConstructible l E S K →
        sfIntegralConstructible l E S ((sfIntegralTwistingFunctor l E S m).obj K)) ∧
      sfIntegralConstructible l E S (sfIntegralTwistingObject l E S m) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E S),
        IsSfDerivedComplete l E S K →
        IsSfDerivedComplete l E S ((sfIntegralTwistingFunctor l E S m).obj K)) ∧
      (∀ K : DerivedCategory (scalarReductionSource l E S),
        finiteTorConstructibleIntegral l E S K →
        finiteTorConstructibleIntegral l E S ((sfIntegralTwistingFunctor l E S m).obj K)) ∧
      (∀ (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S)),
        (∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E S n).obj K) ⊆ Set.Icc a b) →
        ∀ n : ℕ, proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E S n).obj
            ((sfIntegralTwistingFunctor l E S m).obj K)) ⊆ Set.Icc a b) ∧
      (∀ (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S)),
        (∀ n : ℕ, HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E S n).obj K) a b) →
        ∀ n : ℕ, HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E S n).obj
            ((sfIntegralTwistingFunctor l E S m).obj K)) a b) ∧
      (∀ n : ℕ, Nonempty (finiteComplexTwist l E S n m ⋙
        finiteComplexTwist l E S n (-m) ≅ 𝟭 _)) ∧
      Nonempty (sfIntegralTwistingFunctor l E S m ⋙
        sfIntegralTwistingFunctor l E S (-m) ≅ 𝟭 _) ∧
      Nonempty (sfRationalTwistingFunctor l E S m ⋙
        sfRationalTwistingFunctor l E S (-m) ≅ 𝟭 _) ∧
      Nonempty (sfQbarTwistingFunctor l S Ω m ⋙ sfQbarTwistingFunctor l S Ω (-m) ≅ 𝟭 _) := by
  intro m
  have hfinite (n : ℕ) := signedLineTensor_equivalence S
    (integralCoefficientCommRingSheaf l E S n) (purTwistFiniteOne S l E n) m
  have hintegral := signedLineTensor_equivalence S
    (completedIntegralCommRingSheafUnrestricted l E S) (purTwistIntegralModule S l E) m
  have hred := signedTwistReduction_comparison l E S
  have hfin (n : ℕ) : (finiteCoefficientTwist l E S n m).IsFiniteLocallyFreeOfRank 1 :=
    (hfinite n).1
  have htor (n : ℕ) (a b : ℤ)
      (K : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1)))
      (hK : HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1)) K a b) :
      HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
        ((finiteComplexTwist l E S n m).obj K) a b := by
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let := hfin n
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    exact (finiteLineTensor_conditions S _ (finiteCoefficientTwist l E S n m)).2.2 K a b hK
  have hsupp (n : ℕ) (a b : ℤ)
      (K : proEtaleDerivedCategory S (Padic.coefficientExtensionRing l E (n + 1)))
      (hK : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
      proEtaleCohomologicalSupport ((finiteComplexTwist l E S n m).obj K) ⊆ Set.Icc a b := by
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    exact (exact_support_subset S _ (SheafOfModules.siteSheafTensorRight
      (A := integralCoefficientCommRingSheaf l E S n) (finiteCoefficientTwist l E S n m)) K).trans
        hK
  have hcomplete (K : DerivedCategory (scalarReductionSource l E S))
      (hK : IsSfDerivedComplete l E S K) :
      IsSfDerivedComplete l E S ((sfIntegralTwistingFunctor l E S m).obj K) := by
    let := hintegral.1
    have : (SheafOfModules.siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E S)
        (integralTwistLine l E S m)).Additive := integralSheafTwist_additive l E S m
    have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E S)
        (integralTwistLine l E S m)) := integralSheafTwist_finiteLimits l E S m
    have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E S)
        (integralTwistLine l E S m)) := integralSheafTwist_finiteColimits l E S m
    exact integralLineTensor_complete l E S (integralTwistLine l E S m) K hK
  have hireduce (n : ℕ) (K : DerivedCategory (scalarReductionSource l E S)) :=
    (hred.2.2 m n).some.app K
  have hisupp (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S))
      (hK : ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension l E S n).obj K) ⊆ Set.Icc a b) (n : ℕ) :
      proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E S n).obj
        ((sfIntegralTwistingFunctor l E S m).obj K)) ⊆ Set.Icc a b := by
    exact (support_iso S _ (hireduce n K)).symm ▸ hsupp n a b _ (hK n)
  have hitor (a b : ℤ) (K : DerivedCategory (scalarReductionSource l E S))
      (hK : ∀ n : ℕ, HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E S n).obj K) a b) (n : ℕ) :
      HasProEtaleTorAmplitude S (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E S n).obj
          ((sfIntegralTwistingFunctor l E S m).obj K)) a b :=
    tor_of_iso S _ (hireduce n K).symm a b (htor n a b _ (hK n))
  have hiconst (K : DerivedCategory (scalarReductionSource l E S))
      (hK : sfIntegralConstructible l E S K) :
      sfIntegralConstructible l E S ((sfIntegralTwistingFunctor l E S m).obj K) := by
    obtain ⟨hc, a, b, hab, hr⟩ := hK
    refine ⟨hcomplete K hc, a, b, hab, fun n ↦ ⟨?_, ?_⟩⟩
    · exact intrinsic_of_iso l E S n (hireduce n K).symm
        (finite_twist_constructible l E S n m (hfin n) _ (hr n).1)
    · exact hisupp a b K (fun n ↦ (hr n).2) n
  refine ⟨?_, hintegral.1, hred.1, hred.2.1, ?_, ?_, hsupp, htor,
    hiconst, sfIntegralTwistingObject_mem l E S m, hcomplete, ?_, hisupp, hitor, ?_, ?_,
    (fieldTwist_inverse l E S Ω m).1, (fieldTwist_inverse l E S Ω m).2⟩
  · intro n
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let := hfin n
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    exact ⟨hfin n, (finiteLineTensor_conditions S _ (finiteCoefficientTwist l E S n m)).1⟩
  · exact fun n K hK ↦ finite_twist_constructible l E S n m (hfin n) K hK
  · intro n K hK
    obtain ⟨hc, a, b, ht⟩ := hK
    exact ⟨finite_twist_constructible l E S n m (hfin n) K hc, a, b, htor n a b K ht⟩
  · intro K hK
    obtain ⟨hc, a, b, hab, ht⟩ := hK
    exact ⟨hiconst K hc, a, b, hab, hitor a b K ht⟩
  · intro n
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) m).2.2
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) (-m)).1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) (-m)).2.1
    let := (coefficientTwistLine_exact S (purTwistFiniteOne S l E n) (-m)).2.2
    obtain ⟨e⟩ := (hfinite n).2
    exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _⟩
  · obtain ⟨e⟩ := hintegral.2
    let C := integralTowerModules l E S
    have : (𝟭 C).Additive := ⟨fun {_ _} _ _ ↦ rfl⟩
    have : PreservesFiniteLimits (𝟭 C) := inferInstance
    have : PreservesFiniteColimits (𝟭 C) := inferInstance
    exact ⟨Functor.mapDerivedCategoryCompIso (integralSheafTwist l E S m)
      (integralSheafTwist l E S (-m)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (G := 𝟭 (integralTowerModules l E S)) e ≪≫
          Functor.mapDerivedCategoryIdIso _⟩

end WeilConjectures

set_option backward.isDefEq.respectTransparency true

open scoped CategoryTheory.Obj

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private def freeUnitIso (R : C) [MonObj R] : (free R).obj (𝟙_ C) ≅ regular R :=
  isoMk (ρ_ R) (by
    change ((α_ R R (𝟙_ C)).inv ≫ μ[R] ▷ (𝟙_ C)) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    rw [Category.assoc, rightUnitor_naturality]
    monoidal)

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

private noncomputable def extendFreeIso : free R ⋙ extendScalars φ ≅ free S :=
  ((freeForgetAdjunction R).comp (extendRestrictAdjunction φ)).leftAdjointUniq
    (freeForgetAdjunction S)

private noncomputable def extendRegularIso : (extendScalars φ).obj (regular R) ≅ regular S :=
  (extendScalars φ).mapIso (freeUnitIso R).symm ≪≫
    (extendFreeIso φ).app (𝟙_ C) ≪≫ freeUnitIso S

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint

private noncomputable def pullExtendIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    (upperStar Ab.{u + 1} f).mapMod R ⋙
        Mod.extendScalars ((upperStar Ab.{u + 1} f).map a) ≅
      Mod.extendScalars a ⋙ (upperStar Ab.{u + 1} f).mapMod S := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  letI : (upperStar Ab.{u + 1} f).OplaxMonoidal :=
    Functor.Monoidal.toOplaxMonoidal
  letI : adj.IsMonoidal := by
    constructor
    · exact (isMonoidal_upperStarLowerStarAdjunction Ab.{u + 1} f).leftAdjoint_ε
    · intro A B
      exact (isMonoidal_upperStarLowerStarAdjunction Ab.{u + 1} f).leftAdjoint_μ A B
  exact Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} f).map a))
    (Mod.extendRestrictAdjunction a)
    (adj.mapModAdjunction R) (adj.mapModAdjunction S)
    (Mod.comapMapModComapIso (lowerStar Ab.{u + 1} f)
      ((upperStar Ab.{u + 1} f).map a) a
      (adj.unitAlgHom R) (adj.unitAlgHom S) (adj.unit.naturality a))

end AlgebraicGeometry.ProEtale
