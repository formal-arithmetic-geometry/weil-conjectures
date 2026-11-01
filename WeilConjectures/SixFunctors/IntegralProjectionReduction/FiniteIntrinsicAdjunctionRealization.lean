/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport

/-! # Normalized finite adjunction in inverse realization coordinates

Source: Stacks 07A5 and 07A6, localization of the section-normalized adjunction.
(blueprint: lem-sf-finite-intrinsic-adjunction-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open FiniteIntrinsicRealization

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence CategoryTheory.constantSheaf
  HasDerivedCategory.standard AlgebraicGeometry.Scheme.residueField
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence Functor.mapHomologicalComplex
  CompactSupportFiniteProjection.realization sixFunctorFiniteRealization

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
end WeilConjectures.IntegralProjectionReduction
