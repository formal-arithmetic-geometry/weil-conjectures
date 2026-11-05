/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonStrictComparisonAux
public import WeilConjectures.SmoothPurity.IntegralCoherence.SequencePullbackMonoidal
public import WeilConjectures.CategoryTheory.TensorPullbackRepresentativeDescentComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SmoothPurity.Integral.IntegralStrictComparisonComposition
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Composition law of the coherent system pullback/tensor comparison

Source: Stacks 07A4, 0D6D and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent system comparison `pullbackTensorSystemComparison` is written on the
derived inverse image of the sequence-site interface `pullbackTensorSequenceInverse`.
Transporting it along the proved equality with the strict inverse image
`integralComparisonSequencePullback` gives a comparison on the derived strict inverse
images. It is the descent of the generator-normalized strict cochain comparison, and
therefore inherits the strict composition law with the adjunction-normalized compositor.
All maps are maps of entire coefficient systems, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section Square

attribute [local irreducible] pullbackTensorCalculus pullbackTensorSystemModel
  pullbackTensorSequenceCochain coefficientTotalTensor
  CompletedQuotient.pullBridge sequenceDerivedPullbackBridge Functor.mapDerivedCategory
  Functor.leftAdjoint HasDerivedCategory.standard Scheme.residueField

end Square

section Factors

variable {C D F : Type*} [Category C] [Category D] [Category F]
  [Abelian C] [Abelian D] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory F]

end Factors

end WeilConjectures
