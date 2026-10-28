/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.AlgebraicGeometry.VaryingRingOperations
import Sheaf.Paper.NativeOpenTensorOrdinaryCounitEvaluation

/-! # The ordinary counit for native open tensor support

Source: Stacks, Modules on Sites, Tag 0E8I.
(blueprint: lem-coef-native-open-tensor-ordinary-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem coefficientSequence_evaluations_reflect_iso
    {Z : Scheme.{u}} {C D : coefficientSequenceModules l E Z} (f : C ⟶ D)
    (h : ∀ n, IsIso ((coefficientSequenceEvaluation l E Z n).map f)) : IsIso f := by
  let R := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Z))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficientSequenceCommRingSheaf l E Z)
  let T := SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.toPresheaf _
  have hh (U : (ℕ × Z.ProEt)ᵒᵖ) : IsIso ((T.map f).app U) := by
    have := h U.unop.1
    let Tn := SheafOfModules.evaluation.{u + 1}
      (integralCoefficientSheaf l E Z U.unop.1) (op U.unop.2)
    have hn' : IsIso (Tn.map ((coefficientSequenceEvaluation l E Z U.unop.1).map f)) :=
      Functor.map_isIso Tn _
    have hb := ConcreteCategory.bijective_of_isIso
      (Tn.map ((coefficientSequenceEvaluation l E Z U.unop.1).map f))
    exact (ConcreteCategory.isIso_iff_bijective ((T.map f).app U)).mpr hb
  have hT : IsIso (T.map f) := (NatTrans.isIso_iff_isIso_app _).mpr hh
  have hP : IsIso ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map f)) := hT
  have hF : IsIso ((SheafOfModules.forget _).map f) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

/--
The projection-formula counit is invertible for an ordinary tensor with a native
open extension. This is the categorical core of the support argument: the
localized extension/tensor construction gives an inverse on the direct-sum
generators, and the same inverse descends through coefficient quotients.
Source: Stacks, sites-modules.tex, Tag 0E8I, lemma-j-shriek-and-tensor.
(blueprint: lem-coef-native-open-tensor-ordinary-counit).
-/
theorem nativeOpenTensor_ordinary_counit_isIso {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (M : coefficientSequenceModules.{u, u} l E X)
    (N : coefficientSequenceModules.{u, u} l E Z) :
    IsIso ((AlgebraicGeometry.ProEtale.VaryingRing.moduleJAdj
      (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j).counit.app
      (ordinaryTensor.{u + 1, u, u}
        (coefficientSequenceTopology (ProEt.topology Z))
        (coefficientSequenceCommRingSheaf.{u, u} l E Z)
        ((AlgebraicGeometry.ProEtale.VaryingRing.extension
          (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j).obj M) N)) := by
  apply coefficientSequence_evaluations_reflect_iso l E
  intro n
  exact nativeOpenTensor_ordinary_counit_evaluation_isIso l E j M N n

end WeilConjectures.CoefSupportOpenTensor
