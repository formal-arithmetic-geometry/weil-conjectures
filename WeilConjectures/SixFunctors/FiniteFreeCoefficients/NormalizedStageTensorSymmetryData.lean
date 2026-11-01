/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit
import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! Normalized tensorators and Koszul symmetries for all finite stages.

The proof uses the ordinary balanced scalar tensorator, the descended pro-etale
finite Verdier scalar comparison, and their representative Koszul braidings.
The construction works for every ring homomorphism, so no finite-stage factorization
or quotient-cofinality argument is needed for these data. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Etale.ExceptionalCoefficients
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

end WeilConjectures.FiniteFreeCoefficients
