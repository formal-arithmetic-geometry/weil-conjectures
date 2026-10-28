/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels

/-! # Underlying sheaf extensionality for nested scalar tensors

Source: Stacks Project, Tag 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-nested-chosen-scalar-tensor-val-ext)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

/--
Tensor induction and sheafification identify the underlying presheaf maps of two
morphisms in a nested completed scalar extension whenever they agree on nested
pure tensor sections. This is the sectionwise tensor-induction substep; the
categorical equality of morphisms is obtained by `SheafOfModules.hom_ext`.

Source: Stacks 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-nested-chosen-scalar-tensor-val-ext)
-/
theorem nestedChosenScalarTensor_val_ext
    (M : integralTowerModules l E X)
    (Q : integralTowerModules l F X)
    (f g : (completedOrdinaryScalarExtension l L F j X).obj
      ((completedOrdinaryScalarExtension l E L ι X).obj M) ⟶ Q)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : M.val.obj U),
      f.val.app U (completedScalarTensorSection l L F j X
        ((completedOrdinaryScalarExtension l E L ι X).obj M) U s
        (completedScalarTensorSection l E L ι X M U t x)) =
      g.val.app U (completedScalarTensorSection l L F j X
        ((completedOrdinaryScalarExtension l E L ι X).obj M) U s
        (completedScalarTensorSection l E L ι X M U t x))) :
    f.val = g.val := by
  sorry

end WeilConjectures
