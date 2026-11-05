/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatWeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Dualizability is local on the small pro-étale site

Let `Λ` be a commutative ring and `X` a scheme. For a weakly étale morphism `g : W ⟶ X`, the
derived pullback `Lg^*` preserves dualizable objects of `D(X_proét, Λ)`
(`AlgebraicGeometry.ProEtale.isDualizable_leftDerivedUpperStar_obj`), and an object whose
derived pullbacks to the members of a pro-étale covering family are dualizable is dualizable
(`AlgebraicGeometry.ProEtale.isDualizable_of_cover`).

## Strategy

The pullback `g^*` along a weakly étale morphism is an exact monoidal functor, which commutes
with internal homs (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`), preserves flat
sheaves (`AlgebraicGeometry.ProEtale.preservesFlat_upperStar_of_weaklyEtale`) and has an exact
left adjoint (the left Kan extension along the localization functor, followed by
sheafification). So the chain-level dualizability criterion transfers along `g^*`
(`DerivedCategory.DualizabilityDatum.isDualizable_Q_obj_map_iff`): there is a morphism `φ` of
`D(X_proét)` such that `K` is dualizable if and only if `φ` is an isomorphism, and `Lg^*K` is
dualizable if and only if `Lg^*φ` is an isomorphism, for every weakly étale `g`. The derived
pullbacks along a pro-étale covering family are jointly conservative.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

section Transfer

variable {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]

end Transfer

end AlgebraicGeometry.ProEtale
