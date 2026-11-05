/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import Mathlib.RingTheory.Ideal.Maps

/-! # Scalar base change for a finite coefficient module

Source: Stacks Project, Tags 03EK and 03EL.
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
namespace CoefficientBC
universe v r w
variable {C : Type w} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

@[instance_reducible] private def quotientModule {S T M : Type*} [CommRing S] [CommRing T]
    [AddCommGroup M] [Module S M] (q : S →+* T) (hq : Function.Surjective q)
    (hz : ∀ s, q s = 0 → ∀ x : M, s • x = 0) : Module T M where
  smul t x := quotientAction q hq hz t x
  one_smul x := congrArg (fun f : AddMonoid.End M ↦ f x) (map_one (quotientAction q hq hz))
  mul_smul a b x :=
    congrArg (fun f : AddMonoid.End M ↦ f x) (map_mul (quotientAction q hq hz) a b)
  smul_zero t := map_zero (quotientAction q hq hz t)
  smul_add t x y := map_add (quotientAction q hq hz t) x y
  zero_smul x :=
    congrArg (fun f : AddMonoid.End M ↦ f x) (map_zero (quotientAction q hq hz))
  add_smul a b x :=
    congrArg (fun f : AddMonoid.End M ↦ f x) (map_add (quotientAction q hq hz) a b)

variable [EssentiallySmall.{r} C]

end CoefficientBC

attribute [local irreducible] HasDerivedCategory.standard scalarWitness

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures.RamifiedPullback
