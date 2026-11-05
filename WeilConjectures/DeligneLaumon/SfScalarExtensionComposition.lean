/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Composition of intrinsic rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469; current main snapshot sec-proper-base-change/sk-thm-properbasechange,
order 1828 (blueprint: lem-weil-scalar-extension-composition).

The ordinary balanced tensor associator and unit are reused from the legacy module.
Their quotient-completion normalization is transported to the current intrinsic integral
subcategory and then to its raw Hom scalar localization. No identification with the legacy
integral constructibility predicate is assumed.

## Main statements

- `sfRationalScalarComp`: canonical composition on the currently recorded rational stages.
- `sfRationalScalarUnit`: the normalized identity-extension comparison.
- `sfRationalScalar_coherence`: both unit equations and the pentagon.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe r u v

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralScalarExtension integralOrdinaryScalar

section OrdinaryCoherence
attribute [local irreducible] integralCompletedScalarMap integralOrdinaryTensorSection
  integralOrdinaryScalarComp integralOrdinaryScalarUnit
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

end

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

variable
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

end OrdinaryCoherence

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

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  (FG : A ⥤ C) (GH : B ⥤ D) (FGH : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive]
  [FG.Additive] [GH.Additive] [FGH.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
  (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
  (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
  (habcd : Functor.isoWhiskerRight a H ≪≫ b = Functor.isoWhiskerLeft F c ≪≫ d)
end

end DerivedCoherence

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

variable (p : ℕ) (hl : l ≠ p)
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

attribute [local irreducible] sfRationalScalarComp
  sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit

end WeilConjectures
