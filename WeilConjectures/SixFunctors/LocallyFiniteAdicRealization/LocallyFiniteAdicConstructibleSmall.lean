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

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8
* Beilinson–Bernstein–Deligne, *Faisceaux pervers*, 1.3.3–1.3.6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

/-- Essential smallness of the native target, independently of a realization functor.
-/
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
