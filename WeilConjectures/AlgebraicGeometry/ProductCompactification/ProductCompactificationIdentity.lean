/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.OpenExternalTensor.OpenExternalTensorNormalization
import WeilConjectures.SixFunctors.Supporting.ExchangeFunctoriality
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition

/-! # Product compactification and the specified exchange/projection composite

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph: reduction to proper maps
(blueprint: lem-sf-product-compactification-identity).

All arrows below are evaluated in the canonical fixed-scalar presentation of the
finite coefficient category. Origin witnesses only evaluate the supplied compositor
and compactification comparisons; no arrow or comparison is supplied as free data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ProductCompactification

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The recorded projection map, with exact inverse-image coordinates at its target.
Source: def-exchange-projection, projection formula composite
(blueprint: lem-sf-product-compactification-identity). -/
def projection {V W : Scheme.{u}} {h : V ⟶ W} (c : Compactification h)
    (K : FiniteD A V) (N : FiniteD A W) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app N ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (FiniteOpenProduct.tensorMap A V (𝟙 K)
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app N))

/-- The specified compact-support exchange in exact inverse-image coordinates.
Source: def-exchange-projection, chosen-compactification exchange
(blueprint: lem-sf-product-compactification-identity). -/
def exchange {T X Y B : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback p q f g)
    (cf : Compactification f) (K : FiniteD A X) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv.app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj K) ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq cf).app K ≫
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (cf.ofIsPullback sq)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).hom.app K)

end AlgebraicGeometry.ProEtale.ProductCompactification
