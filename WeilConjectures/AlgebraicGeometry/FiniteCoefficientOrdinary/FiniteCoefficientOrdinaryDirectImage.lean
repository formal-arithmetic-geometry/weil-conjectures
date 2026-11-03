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

/-- Packaging of the two canonical natural coefficient maps. The equations specify
extension of the A-counit followed by the B-geometric transpose, using the canonical
restriction/pullback comparison. They determine the maps uniquely, without assuming
flatness, an isomorphism of direct images, or faithfulness of derived restriction.
Source: blueprint statement and proof Step 3
(blueprint: lem-coef-finite-direct-image). -/
structure DirectImageMaps where
  etale : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X),
    R(Etale.lowerStar (ModuleCat.{u + 1} A) f) ⋙ Sheaf.fixedCoefficientDerivedScalarExtension
      (X.smallEtaleTopology) φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension (T.smallEtaleTopology) φ ⋙ R(Etale.lowerStar
        (ModuleCat.{u + 1} B) f)
  etale_counit : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))),
    (L(Etale.upperStar (ModuleCat.{u + 1} A) f)).map
      ((scalarAdjunction (X.smallEtaleTopology) φ).unit.app ((R(Etale.lowerStar (ModuleCat.{u + 1}
        A) f)).obj K)) ≫
    (Etale.leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
      ((Sheaf.fixedCoefficientDerivedScalarExtension (X.smallEtaleTopology) φ).obj
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ).map
      ((L(Etale.upperStar (ModuleCat.{u + 1} B) f)).map ((etale φ f).app K) ≫
        (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension (T.smallEtaleTopology) φ).obj K)) =
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
        (scalarAdjunction (T.smallEtaleTopology) φ).unit.app K
  proetale : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X),
    R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f) ⋙ Sheaf.fixedCoefficientDerivedScalarExtension
      (Scheme.ProEt.topology X) φ ⟶
      Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology T) φ ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} B) f)
  proetale_counit : ∀ {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))),
    (L(ProEtale.upperStar (ModuleCat.{u + 1} A) f)).map
      ((scalarAdjunction (Scheme.ProEt.topology X) φ).unit.app ((R(ProEtale.lowerStar
        (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
      ((Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology X) φ).obj
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K)) ≫
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
      ((L(ProEtale.upperStar (ModuleCat.{u + 1} B) f)).map ((proetale φ f).app K) ≫
        (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
          ((Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology T) φ).obj K)) =
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K ≫
        (scalarAdjunction (Scheme.ProEt.topology T) φ).unit.app K

/-- The specified counit mates exist and are unique as natural transformations on
both sites. Source: blueprint statement, proof Steps 3, 6--8
(blueprint: lem-coef-finite-direct-image).

Proof: on K-flat representatives scalar extension is sheafified tensor. Inverse
image commutes with it by the canonical pullback/tensor comparison. Transpose
extension of the A-counit through the B geometric adjunction. Its scalar-adjunction
unit equation is exactly the displayed normalization; all operations are natural.
Conversely the pulled-back scalar unit is universal, since its scalar/pullback
comparison is invertible. Thus this equation determines the B-counit transpose,
and the geometric hom-equivalence determines the map. Apply on each site and use
natural-transformation extensionality and proof irrelevance for uniqueness. -/
theorem directImageMaps_existsUnique : ∃! d : DirectImageMaps.{u}, True := by
  sorry

/-- Compatibility with geometric composition, written with the actual canonical
right-derived compositor. Source: blueprint proof Step 6
(blueprint: lem-coef-finite-direct-image).

Proof: pullback/scalar-extension comparison respects pullback composition on flat
representatives. Transpose this pasted square through the composite geometric
adjunction. The composite counit is the iterated counit, so mate pasting gives
exactly this equation. It holds on arbitrary complexes on this site. -/
theorem etale_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X Y : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    (directImageMaps.etale φ (f ≫ g)).app K =
      (Sheaf.fixedCoefficientDerivedScalarExtension (Y.smallEtaleTopology) φ).map
        ((Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).inv.app K) ≫
      (directImageMaps.etale φ g).app ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) g)).map ((directImageMaps.etale φ f).app K) ≫
      (Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} B) f g).hom.app
        ((Sheaf.fixedCoefficientDerivedScalarExtension (T.smallEtaleTopology) φ).obj K) := by
  sorry

/-- Compatibility with successive coefficient changes, in particular quotient
maps, after canonical derived tensor reassociation. Source: blueprint proof Step 7
(blueprint: lem-coef-finite-direct-image).

Proof: on K-flat representatives the canonical pullback/tensor comparisons commute
with (P tensor_A B) tensor_B C = P tensor_A C. Apply the C geometric adjunction
to the right side. Naturality moves the second scalar extension past the first
counit, and the B-counit equation replaces its first transpose by scalar extension
of the A-counit. Tensor reassociation identifies this with the transpose for the
composite coefficient map. Injectivity of the geometric hom-equivalence proves
the displayed equality. This computation needs no finiteness or flatness. -/
theorem etale_coefficientComposition
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {T X : Scheme.{u}} (f : T ⟶ X)
    (K : _root_.DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :
    (directImageMaps.etale (ψ.comp φ) f).app K =
      (scalarComposition (X.smallEtaleTopology) φ ψ).inv.app ((R(Etale.lowerStar (ModuleCat.{u +
        1} A) f)).obj K) ≫
      (Sheaf.fixedCoefficientDerivedScalarExtension (X.smallEtaleTopology) ψ).map
        ((directImageMaps.etale φ f).app K) ≫
      (directImageMaps.etale ψ f).app ((Sheaf.fixedCoefficientDerivedScalarExtension
        (T.smallEtaleTopology) φ).obj K) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} C) f)).map ((scalarComposition (T.smallEtaleTopology)
        φ ψ).hom.app K) := by
  sorry

end AlgebraicGeometry.FiniteCoefficientOrdinary
