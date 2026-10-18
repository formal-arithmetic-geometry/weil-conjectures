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
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

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
It is the same canonical balancing comparison as the published
`AlgebraicGeometry.Etale.scalarPullbackIso` (lem-pur-etale-scalar-mate-projection),
whose mate is `AlgebraicGeometry.Etale.scalarMate`: on K-flat flat-term models both
are the termwise balancing map. That module cannot be imported together with
`WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars` (both bring a
declaration of `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`), so the
item states the mate form here.
Source: Stacks 07A4 (blueprint: lem-sfb-etale-proetale-scalar-mate). -/
def scalarPullbackEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  haveI := (scalarPullbackReverse_isIso a f).2
  (asIso (scalarPullbackReverseEtale a f)).symm


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
