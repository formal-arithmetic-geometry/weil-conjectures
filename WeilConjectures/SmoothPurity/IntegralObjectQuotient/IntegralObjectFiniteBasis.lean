/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement

/-! # A normalized basis at one finite coefficient level

Source: Stacks Project, Modules on Sites, Tag 04J0; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9.
(blueprint: lem-pur-integral-object-finite-basis).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe a b r
open CategoryTheory Opposite

namespace WeilConjectures.IntegralFiniteBasisProof
open SheafOfModules
open scoped ChangeOfRings

section ScalarBasis
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

end ScalarBasis
end WeilConjectures.IntegralFiniteBasisProof

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped ChangeOfRings
namespace WeilConjectures.IntegralObjectQuotient

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) (W : X.ProEt) (L : integralTowerModules.{u, u} l E X)
  (e : L.over W ≅
    (SheafOfModules.unit.{u, u + 1, u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).over W)

-- The mate formula retains the distinguished site-adjunction unit.

attribute [local irreducible] finitePullback degreePullbackBasis complexBasis

end WeilConjectures.IntegralObjectQuotient
