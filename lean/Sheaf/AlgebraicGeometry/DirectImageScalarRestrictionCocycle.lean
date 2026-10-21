/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition

/-!
# Coefficient cocycle of the normalized pro-etale derived direct image

Source: Stacks Project, derived.tex, Tag 070Y (`lemma-K-injective-defined`), and the
agent-written coefficient-composition argument in the DAG
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

The comparisons are the specified `fixedScalarRestrictionDirectImage` isomorphisms.
The restriction associators are the existing sectionwise identity isomorphisms localized
termwise as `Sheaf.derivedRestrictScalarsCompIso`. All derived categories are unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The inverse-resolution-map normalization determines the direct-image comparison uniquely.
Source: Stacks Tag 070Y and step 2 of the coefficient cocycle argument
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

The hypothesis is exactly the normalization of the recorded comparison theorem, with
all canonical evaluation identifications displayed. Since the localized direct image
of j is invertible, this equation says the evaluated component is its inverse.

Proof: step 1 uses the small pro-etale site and the ordinary direct image of
`def-weil-pbc-proetale-operations`. Grothendieck abelianness gives K-injective resolutions
by `prop-pur-kinjective-resolutions-exist`. For a K-injective H choose a resolution of
its scalar restriction. The hypothesis and
`lem-weil-proetale-direct-image-restriction-of-scalars` identify both evaluated
components with the inverse of the same localized direct-image resolution map.
Cancel the evaluation isomorphisms. For an arbitrary derived object L, represent it
by a complex and choose a K-injective resolution, giving an isomorphism L -> QH by
`def-weil-abstract-derived-category`. Naturality of both comparisons along this
isomorphism and cancellation give equality at L; extensionality gives equality of
natural isomorphisms. No restriction functor is assumed to preserve K-injectives. -/
theorem fixedScalarRestrictionDirectImage_unique
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (γ : Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) ≅
      R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
    (hγ : ∀
      (H : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ)
      [H.IsKInjective]
      (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
      [I.IsKInjective]
      (j : ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
        (.up ℤ)).obj H ⟶ I) [QuasiIso j],
      QuasiIso (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) ∧
        γ.hom.app (_root_.DerivedCategory.Q.obj H) ≫
            (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
              ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso H).hom ≫
            (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
              (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj H) ≫
            _root_.DerivedCategory.Q.map
              (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) =
          (R((f)_*[ModuleCat.{u + 1} A])).map
              ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
                H) ≫
            (R((f)_*[ModuleCat.{u + 1} A])).map (_root_.DerivedCategory.Q.map j) ≫
            ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorObjQIso I).hom) :
    γ = fixedScalarRestrictionDirectImage φ f := by
  sorry

/-- Successive finite coefficient comparisons satisfy the cocycle with the canonical
restriction associators. Source: Stacks Tag 070Y and steps 1, 3--5 of the DAG argument
(blueprint: lem-sf-direct-image-scalar-restriction-cocycle).

Proof: (1) The three source and target module-sheaf categories are abelian and have
K-injective resolutions by `prop-pur-kinjective-resolutions-exist`. Direct image is
additive and commutes with scalar restriction on sections; restriction is exact by
`lem-weil-proetale-direct-image-restriction-of-scalars` and
`def-pc-sheaf-restrict-scalars`.
(2) Use strict composite restriction functors in the generic theorem. Conjugate beta_chi
by rho_X and rho_Y inverse. For a K-injective H and a resolution a of its doubly
restricted complex, put d = rho_X inverse followed by a. The associators are the
identity on underlying abelian sheaves and commute with direct image. Their derived
identifications are the termwise localizations supplied by
`lem-weil-pbc-exact-functor-derived-factorization`.
(3) Apply `lem-sf-kinjective-derived-map-computation` to the map Q(rho_X) with
resolutions a and d. Its transported map is the identity, so its unique homotopy
representative is the identity. Thus the conjugated beta_chi has exactly the same
inverse-resolution-map normalization as the strict composite comparison.
(4) Apply `lem-sf-normalized-derived-comparison-composition` to the three additive
direct-image functors and the exact restrictions, using the normalizations from
`lem-weil-proetale-direct-image-restriction-of-scalars` and step 3. This gives equality
of the strict composite comparisons on every L, without preservation of K-injectives.
(5) Substitute the conjugated beta_chi and cancel rho_Y inverse followed by rho_Y.
This is the displayed equation, in Lean's left-to-right composition order. -/
theorem fixedScalarRestrictionDirectImage_cocycle
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (φ : A →+* B) (ψ : B →+* C)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C))) :
    (R((f)_*[ModuleCat.{u + 1} A])).map
        ((Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology X)
          (f := φ) (g := ψ) rfl).hom.app L) ≫
      (fixedScalarRestrictionDirectImage (ψ.comp φ) f).hom.app L =
    (fixedScalarRestrictionDirectImage φ f).hom.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ψ).obj L) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((fixedScalarRestrictionDirectImage ψ f).hom.app L) ≫
      (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology Y)
        (f := φ) (g := ψ) rfl).hom.app ((R((f)_*[ModuleCat.{u + 1} C])).obj L) := by
  sorry

end AlgebraicGeometry.ProEtale
