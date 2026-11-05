/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence

/-! # The residue-kernel coefficient sequence

Source: Stacks Project, Tag 0942, proof of lemma-bounded (1), elementary DVR sequence
and constant realization, together with Modules on Sites Tags 093J and 03CY.
(blueprint: lem-sf-strict-dvr-coefficient-sequence)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace StrictDvrCoefficientProof

variable {A : Type u} [CommRing A] (π : A)

section ConstantModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

end ConstantModules

section ConstantCoefficientComparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})]
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v r}]
  (A B : CommRingCat.{max u v r}) (f : A →+* B)

variable (D : CommRingCat.{max u v r}) (g : A →+* D)

end ConstantCoefficientComparison

end StrictDvrCoefficientProof

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

open StrictDvrCoefficientProof

end WeilConjectures
