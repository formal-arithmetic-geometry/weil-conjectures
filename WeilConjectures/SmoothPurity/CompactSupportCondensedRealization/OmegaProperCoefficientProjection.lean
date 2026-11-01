/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealizationSetup
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.OmegaProperCoefficientProjectionHomology

/-! # Algebraic-closure coefficients and proper direct image

The proper factor of the compact-support coefficient comparison.
(blueprint: lem-pur-omega-proper-coefficient-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

attribute [local irreducible] WeilConjectures.CompactSupportCondensedRealization.encodingScalarMap
  WeilConjectures.CompactSupportCondensedRealization.IsIntegralScalarSquare

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.CompactSupportCondensedRealization

/-- The proper counit transpose commutes with finite-valued algebraic-closure coefficients
on bounded constructible inputs.
Source: Bhatt--Scholze 6.8.14(1)--(2), 6.8.15; compact-support realization proof Step 13
(blueprint: lem-pur-omega-proper-coefficient-projection).
Proof: identify E with its finite image under a, using the induced topological field
isomorphism. On profinite test objects the coefficient isomorphisms are postcomposition
with this field isomorphism and its inverse. Their composite with inclusion into the
closure is pointwise the prescribed a, so the scalar units, counits and proper
transposes agree. Finite intermediate fields containing the image form a small filtered
category final among all finite intermediate fields, by taking composita. Choose a
bounded-below complex representing K. The simultaneous coefficient-complex presentation
provides the restricted finite scalar extensions and their inclusion cocone into the
finite-subfield-valued closure extension, with a common lower bound. Finite scalar
extensions are finite free, so the canonical proper coefficient transposes at these
stages are isomorphisms: in a continuous finite basis they are finite direct-sum
comparisons. Restriction of scalars is exact, commutes with proper direct image, and
reflects isomorphisms. Apply bounded-below qcqs pushforward continuity in each homology
degree to the restricted coefficient-complex diagram, since g is proper and hence qcqs. Exact tensor
and exact filtered colimits identify the source homology colimits with closure scalar
extension of the proper image and the target with the proper image of the closure
extension. Right-derived direct image preserves the lower bound. The
presentation theorem's adjunct formula identifies each inclusion with coefficient
extension followed by its counit; naturality of that counit identifies the resulting
colimit map with the displayed condensedPushScalar, rather than an unspecified
isomorphism. Its restricted map is therefore invertible on every homology object, and homology
detects isomorphisms.
No continuity assertion on arbitrary unbounded inputs is used. -/
theorem omegaProperCoefficientProjection_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] (g : X ⟶ Y) [IsProper g]
    (K : CondensedERealization.Constructible E X) :
    IsIso ((condensedPushScalar (omegaMap l E a) g).app K.obj) := by
  rw [DerivedCategory.isIso_iff]
  exact omegaProperCoefficientProjection_homology_isIso l E a g K

end WeilConjectures.CompactSupportCondensedRealization
