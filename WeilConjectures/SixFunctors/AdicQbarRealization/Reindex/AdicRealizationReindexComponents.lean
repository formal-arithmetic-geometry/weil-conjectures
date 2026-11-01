/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicRealizationIntegralReindex
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso

/-! # Integral and rational components of the realization reindexing comparison

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-reindex-components)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (B : RingReindex l X g R S) (E : Index l (PadicAlgCl l))
  (I : IntegralReindex l X g B E)

/-- Agreement with the constructed integral components gives the literal normalization.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-realization-reindex-components).
Proof: calculate the abstract composite component and forget its canonical source
transport. The two prescribed localization transports are canonical equality maps,
so their composite has the same heterogeneous component. -/
theorem realizationAgreement_of_components
    (c : commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ derivedPull l X g B)
    (h : ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y,
      HEq (c.hom.app ((inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K)))
        ((realizationIntegralReindex l g R S B E I).hom.app K)) :
    integralRealizationAgreement l g R S B E I c := by
  exact (realizationIntegralReindexData l g R S B E I).agreement c h

/-- The integral comparison extends uniquely to all rational arrows at one field.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-realization-reindex-components).
Proof: raw scalar localization is a categorical localization. Fully faithful
precomposition extends the constructed integral natural isomorphism, fixing every
component because localization leaves objects unchanged. -/
theorem realizationRationalReindex_existsUnique :
    ∃! c : inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
          ordinary l Y S ⋙ derivedPull l X g B,
      ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y,
        c.hom.app ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K) =
            (realizationIntegralReindex l g R S B E I).hom.app K := by
  let C := sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y
  let O := Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E)
  let : ∀ n : ℤ, (shiftFunctor C n).Additive := fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor C n).Linear O :=
    fun n ↦ sfIntegralConstructibleShift_linear l (Coefficient.{u} l (PadicAlgCl l) E) Y n
  exact ScalarLocalization.naturalIso_of_integral
    (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E))
    (sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E)) _ _
    (realizationIntegralReindex l g R S B E I)

/-- The rational comparison is chosen by a condition fixing every component.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-realization-reindex-components). -/
def realizationRationalReindex :=
  (realizationRationalReindex_existsUnique l g R S B E I).exists.choose

end WeilConjectures.AdicQbarRealization
