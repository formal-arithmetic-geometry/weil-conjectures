/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SixFunctors.RamifiedPullback.TensorProof.RamifiedFiniteTensorSections
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of finite scalar extension and module pullback

Source: Stacks Project, Tags 03CZ and 03EL. Composition of left adjoints
normalizes the two scalar-extension comparison maps on unit generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback

attribute [local irreducible] squareIso

section Tensor
variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
  (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings c N)

end Tensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard scalarWitness
  completedIntegralCoefficientSheafUnrestricted
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback
  Functor.leftAdjoint

section FinitePullback
attribute [local irreducible] integralOperationsPullbackAdjunction

end FinitePullback

end WeilConjectures.RamifiedPullback
