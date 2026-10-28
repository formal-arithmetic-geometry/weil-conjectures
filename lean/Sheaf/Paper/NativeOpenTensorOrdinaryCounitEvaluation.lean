/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.AlgebraicGeometry.VaryingRingOperations

/-! Finite coefficient evaluation of the native ordinary tensor counit.

Source: Stacks, Modules on Sites, Tag 0E8I.
(blueprint: new-coef-native-open-tensor-ordinary-counit-evaluation).
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
The ordinary native open tensor counit is invertible after every coefficient
level evaluation. The proof identifies the evaluated sequence-site adjunction
with the localized ordinary extension adjunction for the corresponding
coefficient quotient and applies the ordinary projection formula of Tag 0E8I.
Source: Stacks, sites-modules.tex, Tag 0E8I, proof on each coefficient quotient.
(blueprint: new-coef-native-open-tensor-ordinary-counit-evaluation).
-/
theorem nativeOpenTensor_ordinary_counit_evaluation_isIso
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : coefficientSequenceModules.{u, u} l E X)
    (N : coefficientSequenceModules.{u, u} l E Z) (n : ℕ) :
    IsIso ((coefficientSequenceEvaluation l E Z n).map
      ((AlgebraicGeometry.ProEtale.VaryingRing.moduleJAdj
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j).counit.app
        (ordinaryTensor.{u + 1, u, u}
          (coefficientSequenceTopology (ProEt.topology Z))
          (coefficientSequenceCommRingSheaf l E Z)
          ((AlgebraicGeometry.ProEtale.VaryingRing.extension
            (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j).obj M) N))) := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
