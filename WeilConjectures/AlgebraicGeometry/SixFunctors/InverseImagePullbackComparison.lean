/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import all WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-!
# Inverse image to finite and completed derived pullback

Source: Stacks Project, Tags 03D6 and 08TC; Bhatt--Scholze, Section 6.5
(blueprint: def-weil-inverse-image-pullback-comparison).

Inverse image is expressed in its canonical sectionwise model for an isomorphism.
All coefficient sheaves, finite reductions, pullbacks, transitions, and the Roos
complex are the recorded constructions. A map chosen below has a unique prescribed
value on every section; no arbitrary comparison or cone is supplied as data.
The index n denotes positive exponent n+1. The integral definition takes precisely
the good representative and resolution used to evaluate the recorded completed pullback.

## Main definitions

- `inverseImageCompletedCoefficientMap`: limit lift of the actual finite structure maps.
- `inverseImageFiniteDerived`, `inverseImageIntegralDerived`: exact module inverse images.
- `inverseImagePullbackComparisonFinite`: the sheafified finite tensor-unit map.
- `inverseImagePullbackComparisonFiniteIntrinsic`: its recorded intrinsic presentation.
- `inverseImageRoosComparisonComplex`: the compatible reductions with zero homotopy.
- `inverseImagePullbackComparison`: the integral map for the chosen resolution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

attribute [local irreducible] HasDerivedCategory.standard

/-- The completed coefficient map is an isomorphism, without a completeness
hypothesis on any module.
Source: Stacks Tags 09A5, 00WX and 03CO
(blueprint: def-weil-inverse-image-pullback-comparison).
Proof: the site equivalence preserves the coefficient limit. Each finite structure
map is invertible by the constant-section normalization. The induced map on limits
is invertible and its projection equations identify it with the displayed limit lift. -/
@[instance] theorem inverseImageCompletedCoefficientMap_isIso :
    IsIso (inverseImageCompletedCoefficientMap l E g) := by
  let F := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  have : PreservesLimitsOfSize.{0, 0} F :=
    (isoSectionwiseInverseImage_equivalence g RingCat.{max u (t + 1)}).2.1
  let α := coefficientDiagramMap l E g
  have : ∀ n, IsIso (α.app n) := fun n ↦
    isoSectionwiseConstantMap_isIso g _
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e := preservesLimitIso F (integralCoefficientSheafSystem l E Y) ≪≫
    HasLimit.isoOfNatIso (asIso α)
  have he : inverseImageCompletedCoefficientMap l E g = e.hom := by
    apply limit.hom_ext
    intro n
    simp only [inverseImageCompletedCoefficientMap, limit.lift_π, e, Iso.trans_hom,
      Category.assoc, HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc]
    rfl
  rw [he]
  infer_instance

attribute [local instance] levelPullbackHasDerivedCategory

attribute [local irreducible] constantSheaf completedIntegralCoefficientSheafUnrestricted
  DerivedCategory.Q

/-- The inverse-image resolution is invertible after localization.
Source: Stacks Tag 05RU (blueprint: def-weil-inverse-image-pullback-comparison).
Proof: exact inverse image preserves the kernels, images and quotients defining
cohomology. It therefore preserves the quasi-isomorphism q. Localization sends
this inverse-image quasi-isomorphism to an isomorphism. -/
@[instance] theorem inverseImageResolution_isIso
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    IsIso (DerivedCategory.Q.map
      (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map q)) := by
  infer_instance

end AlgebraicGeometry.ProEtale
