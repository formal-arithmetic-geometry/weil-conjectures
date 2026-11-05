/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi

import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Composition of rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469 (blueprint: lem-weil-scalar-extension-composition).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u r v

open CategoryTheory

namespace WeilConjectures

section ScalarProofContext

attribute [-instance] integralOperationsCommHasDerivedCategory
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralScalarExtension

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

attribute [local irreducible] integralOrdinaryScalar

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

section OrdinaryCoherence
attribute [local irreducible] integralCompletedScalarMap integralOrdinaryTensorSection
section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
variable
  (F : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
  (h : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
  (hm : ∀ {N N' : SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
    (f : N ⟶ N'), F.map f = eqToHom (h N) ≫
    SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (h N').symm)

attribute [local irreducible] tensorSection

end

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

variable
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

end OrdinaryCoherence

attribute [local irreducible] integralCompletedScalarMap integralOrdinaryTensorSection

section OrdinaryCoherence
attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryScalarUnit

end OrdinaryCoherence

attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryScalarUnit
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryIdIso Functor.mapDerivedCategory

section DerivedCoherence
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (T : A ⥤ A) (F : A ⥤ B)
  [T.Additive] [F.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (u : T ≅ 𝟭 A) (a : T ⋙ F ≅ F)
  (ha : a = Functor.isoWhiskerRight u F ≪≫ Functor.leftUnitor F)

end

section
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) (T : B ⥤ B)
  [T.Additive] [F.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (u : T ≅ 𝟭 B) (a : F ⋙ T ≅ F)
  (ha : a = Functor.isoWhiskerLeft F u ≪≫ Functor.rightUnitor F)

end

end DerivedCoherence

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] rationalScalarHom rationalCoefficientMap

attribute [local irreducible] integralOrdinaryDerivedScalarComp
  integralOrdinaryDerivedScalarUnit integralConstructibleScalarComp
  integralConstructibleScalarUnit rationalOrdinaryScalarComp rationalOrdinaryScalarUnit

attribute [local irreducible] rationalScalarExtension rationalOrdinaryScalarExtension
  rationalOrdinaryComparison

attribute [local irreducible] rationalConstructibleScalarComp
  rationalConstructibleScalarUnit

end ScalarProofContext

end WeilConjectures
