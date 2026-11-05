/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore

/-! # The regular coefficient scalar unit is a quasi-isomorphism

Source: Bhatt--Scholze, Propositions 3.1.10, 3.2.3(1), 4.2.8,
Definition 3.5.2 and Lemma 6.8.2(1)
(blueprint: lem-weil-constant-scalar-unit-quasi-isomorphism).

Positive exponent m is indexed by n = m-1. The strict tower, tensor,
normalized unit and mapping cocone are those of the recorded dependencies.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ConstantScalarUnitQuasiIsomorphism
open ConstantScalarStrictUnit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{t})

-- The pure-tensor and functor APIs below do not need the existence witnesses unfolded.
attribute [local irreducible] integralScalarReductionWitness scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence

end WeilConjectures.ConstantScalarUnitQuasiIsomorphism
