/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Sheaf.AlgebraicGeometry.OpenSectionClopen
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.AlgebraicGeometry.ProperOpenSection
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Paper.EtaleUnboundedRestrictionComparison

/-!
# Coefficient naturality of the proper/open refinement

Source: Stacks Project, more-etale.tex, Tags 0F7I and 0GL6; the explicit
clopen-section and adjunction argument in the blueprint
(blueprint: lem-sf-proper-open-coefficient-refinement).

The auxiliary maps implement exactly the normalizations in the node. Scalar extension
and the K-flat-normalized scalar/pullback comparison are existing constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The canonical tensor/pullback comparison, expressed using exact inverse image.
It transports the existing K-flat-normalized comparison along the canonical
identification of derived inverse image with termwise inverse image.
Source: Stacks 0G7E and 0GL6 (blueprint: lem-sf-proper-open-coefficient-refinement). -/
def properOpenCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (v : W ⟶ T) :
    scalarExtension φ T ⋙ (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙ scalarExtension φ W :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).symm ≪≫
    scalarPullbackIso φ v ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v) _

/-- The inverse open coefficient map, defined by its prescribed open-unit transpose.
Source: Stacks 0GL6 (blueprint: lem-sf-proper-open-coefficient-refinement). -/
def properOpenCoefficientOpenInverse
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        ((scalarExtension φ W).obj M) ⟶
      (scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).homEquiv _ _).symm
      ((scalarExtension φ W).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).unit.app M) ≫
        (properOpenCoefficientPullbackIso φ j).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))

/-- The specified inverse open coefficient map is invertible for arbitrary derived inputs.
Source: Stacks 03DJ, 06YS and 0GL6
(blueprint: lem-sf-proper-open-coefficient-refinement).

Proof: choose a K-flat resolution with flat terms by lem-pc-kflat-resolution.
The ordinary extension/tensor identity of lem-weil-pbc-ringed-slice-extension-tensor
and preservation of sums by the left adjoint show that extension by zero preserves
K-flatness and flat terms: tensor with an acyclic complex, restrict it to the open,
and use exactness of inverse image and extension by zero. Thus scalar extension on
both sides is computed by extension by zero and tensoring the same K-flat resolution
termwise, by lem-pur-derived-change-of-rings. The ordinary comparison sends each
open presheaf summand m tensor b to the corresponding summand of m tensor b and
is invertible before and after sheafification. On restriction to the open its
transpose is Q of the open unit followed by lambda inverse, since the canonical
pullback comparison is normalized on those same representatives. Hence its inverse
is exactly properOpenCoefficientOpenInverse. No coefficient flatness is used. -/
theorem properOpenCoefficientOpenInverse_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    IsIso (properOpenCoefficientOpenInverse φ j M) := by
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  have hu : IsIso adj.unit :=
    isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit _ _
  have : (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.Full :=
    adj.fullyFaithfulLOfIsIsoUnit.full
  have : (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.Faithful :=
    adj.fullyFaithfulLOfIsIsoUnit.faithful
  -- Composite left adjoints give an isomorphism of objects; no normalization is needed.
  let e := (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).comp
      (adj.ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (scalarRestrictionPullbackIso φ j) |>.symm
  have : IsIso (adj.counit.app
      ((scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M))) :=
    adj.isIso_counit_app_of_iso (e.app M)
  -- The target lies in the essential image of the fully faithful open extension.
  unfold properOpenCoefficientOpenInverse
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The open tensor isomorphism with the inverse fixed by the open-unit transpose.
Source: Stacks 0GL6 (blueprint: lem-sf-proper-open-coefficient-refinement). -/
def properOpenCoefficientOpenIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j]
    (M : DerivedCategoryModule A W) :
    (scalarExtension φ T).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj
        ((scalarExtension φ W).obj M) :=
  (@asIso _ _ _ _ (properOpenCoefficientOpenInverse φ j M)
    (properOpenCoefficientOpenInverse_isIso φ j M)).symm

/-- The existing theta-normalized proper/open map, viewed in the unbounded category.
Only the canonical compatibility of bounded and unbounded direct image is inserted.
Source: Stacks 0F7I (blueprint: lem-sf-proper-open-coefficient-refinement). -/
def properOpenComparisonAmbient
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T₁ T₂ X : Scheme.{u}} (v : T₁ ⟶ T₂) [IsProper v]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ v = j₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j₂).mapDerivedCategory.obj K.obj ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) v).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj K.obj) :=
  (properOpenComparison A v j₁ j₂ h K).hom ≫
    (lowerStar (ModuleCat.{u + 1} A) v).rightDerivedFunctorPlusCompatibility.hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategoryPlus.obj K)

/-- Coefficient extension respects the specified proper/open refinement arrow.
Source: Stacks 0F7I and 0GL6, with the explicit clopen-section argument
(blueprint: lem-sf-proper-open-coefficient-refinement).

Proof:
1. Form V = T1 times over T2 X and its section s = (j1,id). By
   lem-weil-pbc-proper-open-section the section is clopen. The actual pullback
   square gives inverse-image/open-extension base change by
   cor-cbc-derived-extension-zero-base-change, and extension composition is
   lem-cbc-extension-zero-composition. The original refinement square need not
   be cartesian. Exactness descends these identifications to derived categories.
2. The clopen sheaf product equivalence of lem-weil-pbc-etale-sheaf-clopen-product
   is also an exact equivalence for modules, complexes and their localizations
   (lem-weil-pbc-localization-universal-property). Thus restriction to s(X) and
   its complement detects derived morphisms. Open extension by b is fully
   faithful since its unit is invertible, using
   lem-weil-pbc-extension-by-zero-adjunction.
3. Compute the normalized open coefficient maps on K-flat flat-term resolutions.
   Extension preserves K-flatness by the tensor identity and its exactness,
   as detailed in properOpenCoefficientOpenInverse_isIso. This works without
   flatness of B over A.
4. On those representatives lambda and beta carry the same generator m tensor b
   to its pulled-back generator with coefficient b. Use
   lem-weil-pbc-ringed-pullback-preserves-kflat,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   lem-weil-pbc-site-derived-tensor-descent and
   lem-weil-pbc-inverse-image-composition-module-linear. Their restrictions on
   s(X), after the open units, therefore agree with the identity of Q_X K.
5. Transpose the specified alpha under inverse-image/direct-image adjunction.
   By lem-cbc-proper-open-interchange-coherence, its theta normalization is the
   map on injective representatives of lem-cbc-proper-support-sheaf-composition.
   Its transpose is the identity on s(X) and zero on the complementary component:
   it is exactly the projection p inverse-image M to s extension-by-zero M.
   This applies to K and Q_X K since both are bounded below.
6. After the scalar and open identifications, both scalar changes of that
   projection are (identity,zero) in the clopen product derived category.
   Scalar extension acts componentwise: glue K-flat resolutions of both
   components using the exact inverse equivalence and tensor the pair with B.
   The source and target are extended from V, so full faithfulness of b extension
   and the product equivalence give equality on T1.
7. Transpose the asserted equality under the unbounded B-geometric adjunction
   from def-kun-projection-formula-map. Counit naturality and the definition of
   chi replace its transpose by beta after Q of the A-projection after lambda.
   Naturality of lambda with respect to alpha gives the left side of step 6.
8. The other transpose is the B-projection after inverse image of beta, the
   right side of step 6. Injectivity of the adjunction Hom equivalence proves
   the required equality. No inverse of chi, bound on Q of a direct image,
   constructibility or finite Tor amplitude is used. -/
theorem properOpenComparison_coefficient_refinement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian T₁] [IsNoetherian T₂]
    (v : T₁ ⟶ T₂) [IsProper v]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ v = j₂)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQ : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj K.obj)) :
    (scalarExtension φ T₂).map (properOpenComparisonAmbient A v j₁ j₂ h K) ≫
        (scalarMate φ v).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory.obj K.obj) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} B) v).map
          (properOpenCoefficientOpenIso φ j₁ K.obj).hom =
      (properOpenCoefficientOpenIso φ j₂ K.obj).hom ≫
        properOpenComparisonAmbient B v j₁ j₂ h ⟨(scalarExtension φ X).obj K.obj, hQ⟩ := by
  sorry

end AlgebraicGeometry.Etale
