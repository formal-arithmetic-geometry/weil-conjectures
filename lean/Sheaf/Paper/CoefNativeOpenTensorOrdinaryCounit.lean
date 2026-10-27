/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.AlgebraicGeometry.VaryingRingOperations

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
  sorry

end WeilConjectures.CoefSupportOpenTensor
