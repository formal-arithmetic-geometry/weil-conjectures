/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicRealizationIntegralReindex
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso

/-! # Integral and rational components of native pullback realization

Source: Bhatt--Scholze, Remark 6.8.15; the raw scalar-localization universal property.
(blueprint: lem-sf-native-pullback-integral-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (O : Operations l p R S) (E : Index l (PadicAlgCl l))
  (I : IntegralComparison l p R S O E)

/-- The integral realization composite, retaining its literal transport normalization.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-realization). -/
structure IntegralNativeRealizationData where
  comparison :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient
  agreement : ∀ a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient,
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y,
      HEq (a.hom.app ((inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K))) (comparison.hom.app K)) →
    IntegralAgreement l p R S O E I a

/-- Construct the integral components using the inverse specified completion unit.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-realization).

Proof: naturality of the completion map and I.completion_hom make I.completion
into a natural isomorphism from ordinary pullback to constructible completed pullback.
Compose the exact finite-stage inclusion identity, R's integral realization, inverse
completion, I's derived balance and inverse S realization. The generic five-factor
composite calculation gives the component formula. Its two canonical source transports
are precisely the literal raw-localization object equalities in IntegralAgreement.
No arbitrary isomorphism of the underlying objects replaces the specified completion map. -/
def nativePullbackIntegralRealization : IntegralNativeRealizationData l p R S O E I := by
  let K := Coefficient.{u} l (PadicAlgCl l) E
  let QX := sfRationalConstructibleLocalization l K X
  let QY := sfRationalConstructibleLocalization l K Y
  let IX := inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let IY := inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E
  let P := constructibleIntegralPullback l K p
  let V := (sfIntegralConstructible l K Y).ι
  let W := (sfIntegralConstructible l K X).ι
  let TX := pbcDerivedExtend (coefficientMap l X R E)
  let TY := pbcDerivedExtend (coefficientMap l Y S E)
  let G := ordinaryIntegralDerivedPull l K p
  let H := ContinuousRational.derivedPull p O.coefficient
  let q : V ⋙ G ≅ P ⋙ W := NatIso.ofComponents (fun K ↦ I.completion K) (by
    intro K L f
    change G.map f.hom ≫ (I.completion L).hom =
      (I.completion K).hom ≫ (integralDerivedPullback l _ p).map f.hom
    rw [I.completion_hom, I.completion_hom]
    exact (ordinaryIntegralCompletionComparison l _ p).naturality f.hom)
  let e : QY ⋙ IY ⋙ commonStageDerivedPullback l (PadicAlgCl l) p = P ⋙ QX ⋙ IX :=
    (congrArg (fun Z ↦ QY ⋙ Z) (realizationPullback_inclusion_eq l p E)).trans
      (congrArg (fun Z ↦ Z ⋙ IX) (realizationPullback_localization_eq l p E))
  let r : (QX ⋙ IX) ⋙ ordinary l X R ≅ W ⋙ TX := by
    unfold ordinary
    exact R.integral E
  let s : (QY ⋙ IY) ⋙ ordinary l Y S ≅ V ⋙ TY := by
    unfold ordinary
    exact S.integral E
  refine ⟨realizationReindexComposite P W V (QX ⋙ IX)
    (QY ⋙ IY ⋙ commonStageDerivedPullback l (PadicAlgCl l) p) (ordinary l X R)
    TX TY G H (QY ⋙ IY ⋙ ordinary l Y S) e r q I.derived.symm s, ?_⟩
  intro a ha K
  refine (ha K).trans ?_
  have ho := Functor.congr_obj (realizationPullback_inclusion_eq l p E) (QY.obj K)
  have hr := Functor.congr_obj (realizationPullback_localization_eq l p E) K
  exact realizationReindexComposite_normalized
    (P := P) (W := W) (V := V)
    (U := QY ⋙ IY ⋙ commonStageDerivedPullback l (PadicAlgCl l) p)
    (R := ordinary l X R) (TX := TX) (TY := TY) (H := G) (N := H)
    (Z := QY ⋙ IY ⋙ ordinary l Y S) (p := q) (i := I.derived.symm) (s := s)
    QX IX e r K ((rationalDerivedPullback l (Coefficient.{u} l (PadicAlgCl l) E) p).obj
      (QY.obj K)) ho hr (I.completion K).inv rfl

/-- The constructed integral components extend uniquely to the raw rational stage.
Source: Bhatt--Scholze, Remark 6.8.15 and the raw localization universal property.
(blueprint: lem-sf-native-pullback-integral-realization).

Proof: raw scalar localization is a categorical localization and leaves objects
unchanged. Fully faithful precomposition therefore lifts the integral natural
isomorphism uniquely, with precisely its prescribed components. This proves naturality
on all fractions without enlarging the category by a Karoubi envelope. -/
theorem nativePullbackRationalRealization :
    ∃! a : inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ ordinary l Y S ⋙
          ContinuousRational.derivedPull p O.coefficient,
      ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y,
        a.hom.app ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K) =
            (nativePullbackIntegralRealization l p R S O E I).comparison.hom.app K := by
  let C := sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y
  let A := Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E)
  let : ∀ n : ℤ, (shiftFunctor C n).Additive := fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor C n).Linear A :=
    fun n ↦ sfIntegralConstructibleShift_linear l (Coefficient.{u} l (PadicAlgCl l) E) Y n
  exact ScalarLocalization.naturalIso_of_integral A C
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E)) _ _
    (nativePullbackIntegralRealization l p R S O E I).comparison

/-- The unique rational comparison with the constructed integral components.
Source: raw scalar localization (blueprint: lem-sf-native-pullback-integral-realization). -/
def nativePullbackRationalComparison :=
  (nativePullbackRationalRealization l p R S O E I).exists.choose

end WeilConjectures.AdicQbarRealization.Proper
