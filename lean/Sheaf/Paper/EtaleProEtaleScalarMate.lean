/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities

/-!
# Scalar mates commute with the etale/pro-etale comparison

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-direct-image.proof.md, finite rings paragraph
(blueprint: lem-sfb-etale-proetale-scalar-mate).

This module contains the item statement and the canonical scalar and direct-image
comparison helpers it uses. The helpers are specialized interfaces for the
recorded tensor-pullback and direct-image comparison nodes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the reverse scalar/pullback
comparison is the inverse scalar-adjunction mate of the exact pro-etale
restriction/pullback square. It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackReverseProEtale
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) a ⟶
      pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a))).symm
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom)).natTrans

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the reverse comparison
on the etale site uses the actual exact restriction/pullback square. It specializes
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Source: Stacks 07A4
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackReverseEtale
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a ⟶
      pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology a))).symm
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom)).natTrans

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the canonical tensor/pullback
comparison is invertible for arbitrary ring maps. This is the constant-coefficient
specialization of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Source: Stacks 07A4 and 0G7E (blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: choose K-flat resolutions with flat terms on either small site. Exact
inverse image preserves these resolutions and commutes with constant-ring scalar
extension. On the representatives the inverse scalar mate is the ordinary
balancing map, since its scalar-unit equation is the ordinary tensor adjunction.
Its inverse is the opposite balancing identification. The pure-tensor and unit
normalizations of the general recorded tensor-pullback comparison identify these
maps with its constant-coefficient specialization. Naturality and localization
extend them to all derived objects, preserving both inverse equations. This proves
invertibility on both sites without flatness of B over A or boundedness. -/
theorem scalarPullbackReverse_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarPullbackReverseProEtale a f) ∧
      IsIso (scalarPullbackReverseEtale a f) := by
  sorry

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the specified forward
pro-etale tensor/pullback isomorphism is the inverse of the actual scalar mate.
It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` and is not arbitrary.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackProEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⋙
        L(upperStar (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) a :=
  haveI := (scalarPullbackReverse_isIso a f).1
  (asIso (scalarPullbackReverseProEtale a f)).symm

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the specified forward
etale tensor/pullback isomorphism is the inverse of the actual scalar mate.
It specializes `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
It reuses the published `AlgebraicGeometry.Etale.scalarPullbackIso`.
The proved private comparison at the end of this file identifies this abbreviation
with the original inverse-mate expression, preserving its canonical normalization.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
abbrev scalarPullbackEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  Etale.scalarPullbackIso a f


/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the canonical inverse-image
square identifies exact termwise inverse images with their left derived functors.
It specializes `sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbientPullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the ambient site/direct-image
comparison is the actual counit mate of the specified inverse-image square.
It specializes `sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbient
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R(Etale.lowerStar (ModuleCat.{u + 1} A) f) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f) :=
  (mateEquiv (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (directImageComparisonAmbientPullbackIso A f).hom)).natTrans

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the ambient canonical
comparison is invertible at every bounded-below input. It specializes
`sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: the site square is the canonical fibre-product square (step 1). Exact inverse
images preserve lower bounds, and termwise localization constructs the displayed square
(step 2). Its derived mate is beta, with the prescribed counit equation (step 3).
For qcqs f, the existing direct-image comparison gives an isomorphism e between the
endpoints. Full faithfulness of comparison inverse image identifies both Hom sets
out of a comparison image with the same etale adjunction Hom set. By the mate formula,
postcomposition with beta is the identity under these identifications. Surjectivity
and injectivity give a two-sided inverse for beta (step 4). The derived classical
equivalence then transports classical bounded-below inputs and all-degree cohomology
continuity across this isomorphism (step 5). Naturality and the triangle
identities identify the ambient mate on D+ with the previously recorded comparison,
including its units, counits, identity and composition normalization (step 6).
No finiteness of A is used in this discrete-coefficient theorem. -/
theorem directImageComparisonAmbient_isIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hJ : ∃ n : ℤ, J.IsGE n) :
    IsIso ((directImageComparisonAmbient A f).app J) := by
  sorry

/-- Item helper for `lem-sfb-etale-proetale-scalar-mate`: the inverse of beta is
taken only at the specified bounded-below input. It specializes
`sk-thm-pe-direct-image-comparison`. Source: Stacks Tag 09A6
(blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def directImageComparisonAmbientIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hJ : ∃ n : ℤ, J.IsGE n) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≅
      R(lowerStar (ModuleCat.{u + 1} A) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J) :=
  haveI := directImageComparisonAmbient_isIso A f J hJ
  asIso ((directImageComparisonAmbient A f).app J)


/-- The two canonical B-linear composites transporting the scalar mate agree.
Source: blueprint main-20261015, scalar-six direct-image proof, finite rings paragraph
(blueprint: lem-sfb-etale-proetale-scalar-mate).

Proof, following the node's five steps:
1. Write C for comparison inverse image and l,p,r,s for the etale/pro-etale
   inverse/direct images. Beta is the mate of the inverse-image square d. Hence
   p(beta) followed by the pro-etale counit is d followed by C of the etale counit.
   The qcqs direct-image comparison is invertible on J and on its scalar extension.
2. On flat-term K-flat representatives, the scalar/pullback comparisons c and delta
   are ordinary balancing maps. Both paths through the site/scalar cube send each
   pure tensor to the same pure tensor. The composition and 2-isomorphism coherence
   of lem-sfb-ringed-derived-monoidal-comparisons and the tensor-pullback comparison
   identify these paths on unbounded derived objects, without coefficient flatness.
3. Precompose the desired equation with scalar extension of beta_A. Transpose both
   resulting maps under p_B ⊣ s_B. For the pro-etale path, naturality of c and the
   A-counit equation replace p_A(beta_A) followed by the pro-etale counit by
   d_A followed by C_X of the etale A-counit.
4. Naturality of delta moves that counit past delta_X. The cube equality of step 2
   then rewrites this transpose as C_X of (c_et followed by scalar extension of
   the A-counit), preceded by d_B and p_B(delta_Y). Every map is B-linear.
5. For the other path, the B-counit equation and naturality of d_B give the same
   expression, using the defining transpose of the etale scalar mate. Injectivity
   of the geometric adjunction Hom equivalence gives equality. Precompose with
   scalar extension of beta_A inverse. Neither scalar mate is inverted and the
   intermediate scalar extension on Y need not be bounded below. -/
theorem etaleProEtale_scalar_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hJ : ∃ n : ℤ, J.IsGE n)
    (_hBJ : ∃ n : ℤ, ((pbcFixedScalarExtension X.smallEtaleTopology a).obj J).IsGE n) :
    (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso a f).hom)).natTrans.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J) ≫
      R(lowerStar (ModuleCat.{u + 1} B) f).map ((pbcComparisonReduction X a).hom.app J) =
    (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).map
        (directImageComparisonAmbientIso A f J hJ).inv ≫
      (pbcComparisonReduction Y a).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
        ((mateEquiv
          (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
          (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
          (TwoSquare.mk _ _ _ _ (scalarPullbackEtaleIso a f).hom)).natTrans.app J) ≫
      (directImageComparisonAmbient B f).app
        ((pbcFixedScalarExtension X.smallEtaleTopology a).obj J) := by
  sorry


end AlgebraicGeometry.ProEtale


open scoped CategoryTheory.Functor

private theorem cachedEtaleGroth (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance
private theorem cachedEtaleSheafify (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance
private theorem cachedEtaleMonoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleCoproducts (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasCountableCoproducts (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleFlatResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasFunctorialFlatResolution (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleInjectiveResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasKInjectiveResolutions (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleExactColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleTensor4 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem cachedEtaleTensor12 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensor23 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensorColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).obj V) :=
  inferInstance
private theorem cachedEtaleTensorFlipColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj V) :=
  inferInstance


namespace AlgebraicGeometry.ProEtale
private def scalarPullbackEtaleIsoFromMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  haveI := (scalarPullbackReverse_isIso a f).2
  (asIso (scalarPullbackReverseEtale a f)).symm
end AlgebraicGeometry.ProEtale

section CanonicalScalarPullbackIdentification

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local instance] cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso

private theorem inverse_normalization
    {C : Type*} [Category C] {U V W Z : C} (e : U ≅ V)
    (a : V ⟶ W) (b : U ⟶ Z) (c : Z ≅ W)
    (h : e.hom ≫ a = b ≫ c.hom) : e.inv ≫ b = a ≫ c.inv := by
  apply (cancel_mono c.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem complex_square_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P =
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).symm).hom.app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_obj]
  exact (Category.comp_id _).symm

namespace CategoryTheory.Functor
private theorem square_cochain_fac {A B B' E : Type*} [Category A] [Category B] [Category B']
  [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : CochainComplex A ℤ) :
    F₂.mapDerivedCategoryFactors.inv.app ((F₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app X) ≫
        (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app X) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj X) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app X) := by
  have hF := mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ X
  have hG := mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ X
  have he := mapDerivedCategoryNatIso_fac e X
  have hF' : F₂.mapDerivedCategoryFactors.inv.app
        ((F₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app X) ≫
      (mapDerivedCategoryCompIso F₁ F₂).inv.app (DerivedCategory.Q.obj X) =
        (F₁ ⋙ F₂).mapDerivedCategoryFactors.inv.app X := by
    apply (cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactors.hom.app X)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [← hF, Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rfl
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG, he, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

private theorem unit_symm_homEquiv
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y : D} (h : X ⟶ G.obj Y) :
    adj.unit.app X ≫ G.map ((adj.homEquiv X Y).symm h) = h := by
  exact (adj.homEquiv X Y).apply_symm_apply h

private theorem representative_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory C ⥤ DerivedCategory D) (e : L ≅ F.mapDerivedCategory)
    (τ : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hτ : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ F.mapDerivedCategoryFactorsh.hom = τ)
    (P : CochainComplex C ℤ) :
    τ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) =
        e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P := by
  rw [← hτ]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryFactorsh_hom_app]
  have hq (P : CochainComplex (C) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app P = 𝟙 _ := rfl
  have hq' (P : CochainComplex (D) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app P = 𝟙 _ := rfl
  rw [hq, hq']
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem ordinary_reverse_of_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {sx : A ⥤ B} {rx : B ⥤ A} (ax : sx ⊣ rx)
    {st : C ⥤ D} {rt : D ⥤ C} (at' : st ⊣ rt)
    {f : A ⥤ C} {rf : C ⥤ A} (af : f ⊣ rf)
    {g : B ⥤ D} {rg : D ⥤ B} (ag : g ⊣ rg)
    (e : rx ⋙ f ≅ g ⋙ rt) (δ : rg ⋙ rx ≅ rt ⋙ rf)
    (hδ : (mateEquiv ag af (TwoSquare.mk _ _ _ _ e.hom)).natTrans = δ.hom) :
    ((mateEquiv ax at').symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans =
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv := by
  apply (mateEquiv ax at').injective
  apply (mateEquiv ag af).injective
  rw [Equiv.apply_symm_apply]
  apply TwoSquare.ext
  intro M
  have h := iterated_mateEquiv_conjugateEquiv ax at' af ag
    (TwoSquare.mk _ _ _ _
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv)
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at h hδ
  rw [h, hδ]
  simp only [conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  erw [Equiv.apply_symm_apply]


namespace AlgebraicGeometry.Etale
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local instance] cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

attribute [local irreducible] upperStar
attribute [-instance] ProEtale.pbcRestriction_isRightAdjoint
private theorem scalarRightAdjoint {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).IsRightAdjoint :=
  ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology φ
attribute [local instance] scalarRightAdjoint
private theorem ordinary_reverse_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T)).symm
        (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans =
      (scalarSheafPullbackIso φ f).inv := by
  unfold scalarSheafPullbackIso
  exact ordinary_reverse_of_mate
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarRestrictScalarsIsoSheaf φ f) (lowerStarCompRestrictScalarsIso φ f)
    (underived_mate φ f)

private def scalarCochainUnit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    P ⟶ ((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
    (NatTrans.mapHomologicalComplex
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit (.up ℤ)).app P ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ProEtale.etaleSheafExtendScalars φ T ⋙
        Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).inv.app P

attribute [local irreducible] scalarExtensionRepresentative scalarGeometricRepresentative
  scalarRestrictionPullbackIso ProEtale.scalarPullbackReverseEtale

private theorem geometric_rep_eq {A : Type (u + 1)} [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat A)) ℤ) :
    scalarGeometricRepresentative A f P =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        (DerivedCategory.Q.obj P) ≫
      (upperStar (ModuleCat A) f).mapDerivedCategoryFactors.hom.app P := by
  unfold scalarGeometricRepresentative
  exact representative_eq (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac P

private theorem scalar_rep_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).unit.app
        (_root_.DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (scalarExtensionRepresentative φ T P) =
    _root_.DerivedCategory.Q.map
      (scalarCochainUnit φ T P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
        (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) := by
  let := ProEtale.pbcRestriction_isRightAdjoint T.smallEtaleTopology φ
  unfold scalarCochainUnit scalarExtensionRepresentative
  exact unit_symm_homEquiv (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) _

private theorem scalar_complex_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map
      (scalarCochainUnit φ X P) ≫
      ((Functor.mapHomologicalComplexCompIso (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (upperStar (ModuleCat.{u + 1} B) f ⋙
            Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).symm).hom.app
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P)) =
    scalarCochainUnit φ T
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).map
        ((scalarSheafPullbackComplexIso φ f).inv.app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  change (upperStar (ModuleCat.{u + 1} A) f).map
      (𝟙 _ ≫ (ProEtale.etaleSheafExtendScalarsAdjunction φ X).unit.app (P.X i) ≫ 𝟙 _) ≫
      ((upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((ProEtale.etaleSheafExtendScalars φ X).obj (P.X i)) ≫ 𝟙 _) =
    (𝟙 _ ≫ (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app
      ((upperStar (ModuleCat.{u + 1} A) f).obj (P.X i)) ≫ 𝟙 _) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        (𝟙 _ ≫ (scalarSheafPullbackIso φ f).inv.app (P.X i))
  simp only [Category.id_comp, Category.comp_id]
  let M := P.X i
  have h := unit_mateEquiv_symm
    (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom) M
  change (upperStar (ModuleCat.{u + 1} A) f).map
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).unit.app M) ≫
      (upperStarRestrictScalarsIsoSheaf φ f).hom.app
        ((ProEtale.etaleSheafExtendScalars φ X).obj M) =
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app
      ((upperStar (ModuleCat.{u + 1} A) f).obj M) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        (((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ X)
          (ProEtale.etaleSheafExtendScalarsAdjunction φ T)).symm
          (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans.app M) at h
  rw [ordinary_reverse_eq] at h
  exact h

private theorem restriction_geometric_fac
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) f).map
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app P) ≫
      (scalarRestrictionPullbackIso φ f).hom.app (_root_.DerivedCategory.Q.obj P) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map
        (scalarGeometricRepresentative B f P) ≫
      (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app
        (((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj P) =
    scalarGeometricRepresentative A f
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (upperStar (ModuleCat.{u + 1} B) f ⋙
              Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).symm).hom.app P) := by
  rw [geometric_rep_eq, geometric_rep_eq]
  unfold scalarRestrictionPullbackIso
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  erw [(leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.naturality_assoc]
  have h :
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.inv.app
          (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app P) ≫
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.map
          ((upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategoryFactors.hom.app P) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app
          (((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj P) =
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (upperStarRestrictScalarsIsoSheaf φ f).hom (.up ℤ)).app P) :=
    CategoryTheory.Functor.square_cochain_fac (upperStarRestrictScalarsIsoSheaf φ f) P
  have hh := congrArg
    (fun z ↦ (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom.app
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) ≫ z) h
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc] at hh
  rw [hh]
  apply congrArg (fun z ↦
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
      (DerivedCategory.Q.obj
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex
          (.up ℤ)).obj P)) ≫
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom.app
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex
        (.up ℤ)).obj P) ≫ z)
  rw [← DerivedCategory.Q.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact complex_square_hom (upperStarRestrictScalarsIsoSheaf φ f) P

private theorem geometric_rep_naturality
    (A : Type (u + 1)) [CommRing A] {T X : Scheme.{u}} (f : T ⟶ X)
    {P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (g : P ⟶ Q) :
    L(upperStar (ModuleCat.{u + 1} A) f).map (_root_.DerivedCategory.Q.map g) ≫
      scalarGeometricRepresentative A f Q =
    scalarGeometricRepresentative A f P ≫ _root_.DerivedCategory.Q.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map g) := by
  simp only [geometric_rep_eq, Category.assoc]
  have h := (Functor.whiskerLeft _root_.DerivedCategory.Q
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom ≫
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors.hom).naturality g
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Category.assoc] using h

private theorem reverse_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (ProEtale.scalarPullbackReverseEtale φ f).app (_root_.DerivedCategory.Q.obj P) ≫
      L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ X P) ≫
      scalarGeometricRepresentative B f
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P) =
    (scalarExtension φ T).map (scalarGeometricRepresentative A f P) ≫
      scalarExtensionRepresentative φ T
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).inv.app P) := by
  let adx : scalarExtension φ X ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
    Adjunction.ofIsRightAdjoint _
  let adt' : scalarExtension φ T ⊣ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ :=
    Adjunction.ofIsRightAdjoint _
  let ec := Functor.mapHomologicalComplexCompIso (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar (ModuleCat.{u + 1} B) f ⋙
        Sheaf.restrictScalars T.smallEtaleTopology φ)) (.up ℤ)).symm
  unfold ProEtale.scalarPullbackReverseEtale
  change ((mateEquiv adx adt').symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)).natTrans.app
      (DerivedCategory.Q.obj P) ≫ _ = _
  let kd := ((mateEquiv adx adt').symm (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ
    f).hom)).natTrans
  have hk := scalar_complex_unit φ f P
  have hkd := unit_mateEquiv_symm adx adt' (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ
    f).hom) (_root_.DerivedCategory.Q.obj P)
  change L(upperStar (ModuleCat.{u + 1} A) f).map (adx.unit.app (_root_.DerivedCategory.Q.obj P)) ≫
    (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ X).obj
    (_root_.DerivedCategory.Q.obj P)) =
    adt'.unit.app (L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P)) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map (kd.app
      (_root_.DerivedCategory.Q.obj P)) at hkd
  have hef (N : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) : L(upperStar
    (ModuleCat.{u + 1} A) f).map ((Sheaf.restrictScalars X.smallEtaleTopology
    φ).mapDerivedCategoryFactors.inv.app N) ≫ (scalarRestrictionPullbackIso φ f).hom.app
    (_root_.DerivedCategory.Q.obj N) ≫
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map (scalarGeometricRepresentative B f
        N) =
        scalarGeometricRepresentative A f (((Sheaf.restrictScalars X.smallEtaleTopology
          φ).mapHomologicalComplex (.up ℤ)).obj N) ≫ _root_.DerivedCategory.Q.map (ec.hom.app N) ≫
          (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app
          (((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj N) := by
    have h := congrArg (fun z ↦ z ≫ (Sheaf.restrictScalars T.smallEtaleTopology
      φ).mapDerivedCategoryFactors.inv.app (((upperStar (ModuleCat.{u + 1} B)
      f).mapHomologicalComplex (.up ℤ)).obj N)) (restriction_geometric_fac φ f N)
    simpa only [Functor.comp_obj, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id] using h
  apply (adt'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% hkd]
  erw [← (scalarRestrictionPullbackIso φ f).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← L(upperStar (ModuleCat.{u + 1} A) f).map_comp_assoc, (scalar_rep_unit φ X P), L(upperStar
    (ModuleCat.{u + 1} A) f).map_comp, Category.assoc, hef]
  have hnat := geometric_rep_naturality A f (scalarCochainUnit φ X P)
  rw [reassoc_of% hnat]
  rw [← _root_.DerivedCategory.Q.map_comp_assoc, hk]
  simp only [Functor.map_comp, Category.assoc]
  erw [(Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.naturality]
  simp only [Functor.comp_map]
  erw [← adt'.unit.naturality_assoc]
  simp only [Functor.id_map]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [reassoc_of% (scalar_rep_unit φ T (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
    (.up ℤ)).obj P))]

private theorem scalarPullback_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T X : Scheme.{u}} (f : T ⟶ X) :
    ProEtale.scalarPullbackEtaleIsoFromMate φ f = scalarPullbackIso φ f := by
  apply (scalarPullbackIso_existsUnique φ f).choose_spec.2
  intro P _hP
  have := (ProEtale.scalarPullbackReverse_isIso φ f).2
  have h := inverse_normalization
    ((asIso (ProEtale.scalarPullbackReverseEtale φ f)).app (_root_.DerivedCategory.Q.obj P))
    (L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ X P) ≫
      scalarGeometricRepresentative B f
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj P))
    ((scalarExtension φ T).map (scalarGeometricRepresentative A f P) ≫
      scalarExtensionRepresentative φ T
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P))
    (_root_.DerivedCategory.Q.mapIso ((scalarSheafPullbackComplexIso φ f).app P).symm)
    (by simpa only [Iso.app_hom, Iso.app_inv, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc] using reverse_normalization φ f P)
  simpa only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc] using h

end AlgebraicGeometry.Etale

end CanonicalScalarPullbackIdentification

attribute [instance] AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint

namespace AlgebraicGeometry.ProEtale
/-- The reused normalized comparison is the original inverse scalar mate.
Source: Stacks 07A4, 0G7E and 07A7
(blueprint: lem-sfb-etale-proetale-scalar-mate).
Proof: the ordinary reverse mate equals the inverse ordinary scalar/pullback
comparison by iterated mates and the restriction/direct-image adjunction identity.
Its scalar-unit equation holds degreewise on cochains. The exact derived geometric
representatives commute with the localized restriction square. Taking the derived
scalar adjunction transpose proves the reverse normalization. Invert that equation
and use uniqueness of the normalized forward comparison on K-flat representatives.
All helpers above prove these equations, with no additional hypotheses or holes. -/
private theorem scalarPullbackEtaleIso_eq_fromMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarPullbackEtaleIso a f = scalarPullbackEtaleIsoFromMate a f := by
  exact (Etale.scalarPullback_eq a f).symm
end AlgebraicGeometry.ProEtale
