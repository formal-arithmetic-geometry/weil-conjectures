/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition

/-! # Quotient transitions on K-flat representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionDerivedExistence normalizedDVRResCompletedComp
  scalarReductionDerivedExtension scalarReductionCounit

section AdjunctionHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {S : C ⥤ A}
  (H : C ⥤ B) (i : H ⋙ R ≅ S) (adj : F ⊣ R) (adjn : G ⊣ S)

end AdjunctionHelpers

section TensorHelpers
universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S T : Sheaf J CommRingCat.{r}}
  (f : R ⟶ S) (g : R ⟶ T) (q : S ⟶ T) (hq : f ≫ q = g)
open SheafOfModules.UnrestrictedTowerProof

variable
  (F : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (G : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
  (hf : ∀ N, F.obj N = SheafOfModules.changeOfRings f N)
  (hg : ∀ N, G.obj N = SheafOfModules.changeOfRings g N)

attribute [local irreducible] finiteMap tensorRestrictionComp

end TensorHelpers

attribute [local irreducible] SheafOfModules.changeOfRings
  SheafOfModules.changeOfRingsHom

attribute [local irreducible] SheafOfModules.UnrestrictedTowerProof.identifiedMap
  SheafOfModules.UnrestrictedTowerProof.sheafMap
  SheafOfModules.UnrestrictedTowerProof.restrictedMap
  SheafOfModules.UnrestrictedTowerProof.tensorSection

section ExactHelpers
universe a b c v w z
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v} A] [Category.{w} B] [Category.{z} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (H : A ⥤ B) (R : B ⥤ C) (S : A ⥤ C)
  [H.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (i : H ⋙ R ≅ S)

end ExactHelpers

attribute [local irreducible] Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
attribute [local instance] normalizedDVRKFlatTransitionLocal1
attribute [local instance] normalizedDVRKFlatTransitionLocal2

attribute [local irreducible] normalizedDVRKFlatComparison

attribute [local instance] scalarReductionExtensionAdditive
  scalarReductionRestrictionLimits scalarReductionRestrictionColimits

attribute [local irreducible] normalizedDVRQuotient integralCoefficientSheafTransition

attribute [local irreducible] scalarReductionExistence unrestrictedIntegralReductionExistence
  scalarReductionExtension unrestrictedIntegralReductionFunctor

attribute [local irreducible] finiteModuleStep

attribute [local irreducible] moduleRestrictionComp

section TensorIdentification
attribute [local semireducible] scalarReductionExistence unrestrictedIntegralReductionExistence
  scalarReductionExtension unrestrictedIntegralReductionFunctor

end TensorIdentification

end WeilConjectures
