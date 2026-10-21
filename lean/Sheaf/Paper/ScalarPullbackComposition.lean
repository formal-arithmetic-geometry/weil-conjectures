/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Composition coherence of the normalized scalar/pullback comparison

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D, and sites-modules.tex, Tag 03D8
(blueprint: lem-sf-scalar-pullback-composition).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The normalized scalar/pullback comparison commutes with composition of inverse images.
The displayed transports express left-derived inverse images as the levelwise exact functors.
Source: Stacks Project, Tag 0D6D (lemma-derived-pullback-composition), with the ordinary
composition of Tag 03D8 and the K-flat pullback calculation of Tag 0G7E
(blueprint: lem-sf-scalar-pullback-composition).

Proof: take a flat-term K-flat resolution P of N. Pullback preserves K-flatness and flat
terms, so the normalization of scalarPullbackIso applies both to P and to v inverse-image P.
Compute the two sides using these normalizations and the localization factorization
identities for mapDerivedCategoryNatIso and mapDerivedCategoryCompIso. The resulting
ordinary square is the scalar/pullback composition square: both routes pull back the
same tensor generator m tensor b to its twice pulled-back generator with coefficient b.
This is the ordinary ringed-pullback composition identification of Tag 03D8, with constant
coefficient change regarded as a morphism of ringed topoi over the identity. The maps are
linear, agree after sheafification, and commute with differentials, so their images under
localization agree. The representative counits on these K-flat models are invertible;
cancel them to obtain the equality at Q(P). Naturality along the resolution isomorphism
Q(P) to N yields the displayed equality. No ring map is assumed flat; no complex is assumed
bounded. For an empty source, a zero object, or a zero coefficient ring, the same argument
holds in the zero category. Identity scheme maps give the unit case of the same ordinary
composition identity. -/
theorem scalarPullback_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app ((scalarExtension φ T₂).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory.map
        ((Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).symm ≪≫
        scalarPullbackIso φ v ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v) _).hom.app N) ≫
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₁).symm ≪≫
        scalarPullbackIso φ j₁ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₁) _).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₂).symm ≪≫
        scalarPullbackIso φ j₂ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₂) _).hom.app N ≫
        (scalarExtension φ X).map
          ((Functor.mapDerivedCategoryNatIso
              (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app N) := by
  sorry

end AlgebraicGeometry.Etale
