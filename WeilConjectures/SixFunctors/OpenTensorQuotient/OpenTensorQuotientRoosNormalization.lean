/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-! # Roos normalization of scalar-unit tensor augmentations

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, 3.4.10
* [Stacks, Tag 03EK]
* [Stacks, Tag 06YN]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Every scalar-unit augmentation is the first coordinate of the fixed normalized
Roos tensor-completion chain map. -/
theorem augmentation_roos_normalized (W : Scheme.{u})
    (t : OpenFactorCoherence.Tensor l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (a : Augmentation l E W P Q) : RoosNormalization l E W t P Q a := by
  intro n i
  apply heq_of_eq
  have h : a.map.app (op n) =
      t.chain.app (P, Q) ≫ CochainComplex.mappingCocone.fst
        (constructibleTensorBoundary l E W P Q) ≫
        Pi.π (fun k ↦ (integralOperationsTensorLevel l E W k).obj (P, Q)) n := by
    apply HomologicalComplex.hom_ext
    intro k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    subst k
    apply AlgebraicGeometry.Scheme.tensor_hom_ext W
      (completedIntegralCommRingSheafUnrestricted l E W) _ _
    intro V x y
    exact (a.sections n p q V x y).trans (t.canonical.1.1 P Q p q n V x y).symm
  exact congrArg (fun f ↦ f.f i) h

end WeilConjectures.OpenTensorQuotient
