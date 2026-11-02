/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Ordinary direct image and arbitrary finite coefficient change

Source: latest Weil blueprint, sec-smooth-purity/sk-lem-sp-tower,
`lem-coef-finite-direct-image.md` and its proof (blueprint: lem-coef-finite-direct-image).
The coefficients are arbitrary finite rings killed by a power of ell, not only stages
of a chosen coefficient tower. Canonical maps are fixed by the scalar-unit/counit
equation, in the ordinary module derived categories, on both small sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.FiniteCoefficientOrdinary

attribute [local instance] Scheme.Etale.essentiallySmall

/-- The adjunction of ordinary derived scalar extension, with its existing exact
restriction functor. Source: Stacks 06YY, 06XN and blueprint
(blueprint: lem-coef-finite-direct-image), coefficient-map specification. -/
def scalarAdjunction {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    Sheaf.fixedCoefficientDerivedScalarExtension J φ ⊣ Sheaf.derivedRestrictScalars J φ :=
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint J φ
  Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)

/-- Canonical tensor reassociation, defined by the restriction-composition identity.
Source: Stacks 06YY and blueprint proof, coefficient-chain paragraph
(blueprint: lem-coef-finite-direct-image). -/
def scalarComposition {D : Type (u + 1)} [Category.{u} D]
    [EssentiallySmall.{u + 1} D] (J : GrothendieckTopology D)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    Sheaf.fixedCoefficientDerivedScalarExtension J φ ⋙
      Sheaf.fixedCoefficientDerivedScalarExtension J ψ ≅
        Sheaf.fixedCoefficientDerivedScalarExtension J (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (scalarAdjunction J φ) (scalarAdjunction J ψ)
    (scalarAdjunction J (ψ.comp φ)) (Sheaf.derivedRestrictScalarsCompIso J rfl)

end AlgebraicGeometry.FiniteCoefficientOrdinary
