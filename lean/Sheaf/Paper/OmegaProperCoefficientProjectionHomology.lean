/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.CompactSupportCondensedRealizationSetup

/-! # Homology-level proper coefficient projection

The proper coefficient comparison is invertible on every homology object.
(blueprint: lem-pur-omega-proper-coefficient-projection-homology).
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

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.CompactSupportCondensedRealization

/--
The proper coefficient comparison induces an isomorphism on every homology object
of a bounded constructible input.

Source: Bhatt--Scholze 6.8.14(1)--(2), 6.8.15; compact-support realization proof
Step 13 (blueprint: lem-pur-omega-proper-coefficient-projection-homology).

Proof: identify the finite image of the coefficient embedding, express the closure
coefficient as the filtered colimit of finite intermediate fields, and choose a common
lower bound for the coefficient-complex presentation. At each finite stage the
restricted coefficient module is finite free, so the proper coefficient transpose is
a finite direct-sum comparison and is invertible. Bounded-below qcqs pushforward
continuity identifies the homology of the colimit comparison with the colimit of
these finite-stage isomorphisms. Exact scalar extension and filtered colimits identify
that colimit with the displayed homology map of `condensedPushScalar`; hence this map
is invertible in every degree. -/
theorem omegaProperCoefficientProjection_homology_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] (g : X ⟶ Y) [IsProper g]
    (K : CondensedERealization.Constructible E X) :
    ∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((condensedPushScalar (omegaMap l E a) g).app K.obj)) := by sorry

end WeilConjectures.CompactSupportCondensedRealization
