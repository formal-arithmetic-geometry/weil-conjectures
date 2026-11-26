/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleSheafSmall
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # LocallyFiniteAdicConstructibleSmall

The native bounded constructible derived category is essentially small.

## Implementation details

A small family of native constructible modules (from
`constructibleModuleObjects_essentiallySmall`), together with all integer shifts, builds
every bounded constructible object through `exists_bounded_postnikov_tower`;
`essentiallySmall_extensionProduct` bounds the middle objects at each extension step.

## References

* [Bhatt--Scholze, Section 6.8]
* [BBD, 1.3.3--1.3.6]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- Essential smallness of the native target, independently of a realization functor. -/
theorem nativeConstructible_essentiallySmall
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X] :
    EssentiallySmall.{u + 1}
      (ProEtale.DerivedCategory.boundedAdicConstructible l X).FullSubcategory := by
  have : ObjectProperty.EssentiallySmall.{u + 1} (ProEtale.adicConstructibleSheaf l X) :=
    nativeConstructibleSheaf_essentiallySmall l X
  have : ObjectProperty.EssentiallySmall.{u + 1}
      (ProEtale.DerivedCategory.boundedAdicConstructible l X) :=
    DerivedCategory.essentiallySmall_bounded_inf (ProEtale.adicConstructibleSheaf l X)
  infer_instance

end WeilConjectures.LocallyFiniteAdicRealization
