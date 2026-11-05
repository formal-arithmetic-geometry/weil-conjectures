/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenUnitEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Data for normalized open extension, tensor and base change

Source: Stacks 03DI, 0F6Z, 0E8I, 0GL1 and the open-factor sentence of
`fix-prop-coherence` (blueprint: lem-sf-open-tensor-normalization).
All operation presentations below are conclusions of the theorem, not hypotheses.
-/

-- Owning definition node (blueprint: def-sf-open-normalization-data).

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
set_option linter.checkUnivs false

universe u v h w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules.OpenTensorNormalization

-- The following vertical-sieve calculation is the universe-independent version of
-- DiagramSiteTopology: Stacks 00Z4 and 00Z8. Only proof helpers are introduced.

attribute [instance] baseChange_continuous openInclusion_continuous

attribute [instance] Pullback.additive

attribute [instance] OpenExtension.additive OpenExtension.limits OpenExtension.colimits

attribute [instance] FiniteRealization.additive

namespace FiniteTensorPin

variable {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {e : FiniteRealization A X R i} {t : TensorModel R}
    {d : finiteTensor A X ⋙ e.derived ≅ (e.derived.prod e.derived) ⋙ t.functor}

end FiniteTensorPin

end SheafOfModules.OpenTensorNormalization
