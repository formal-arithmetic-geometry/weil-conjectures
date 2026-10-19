/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Tensor normalization of a scalar/pullback comparison

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 07A7;
more-etale.tex, Tag 0GL6
(blueprint: lem-pur-scalar-tensor-pullback-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Forgetting the coefficients in a representative-normalized scalar/pullback
comparison gives the specified monoidal pullback comparison, with the coefficient
object identified by exact inverse image and its monoidal unit.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 0G7E and 07A7;
more-etale.tex, Tag 0GL6; step 2 of lem-pur-etale-scalar-mate-projection
(blueprint: lem-pur-scalar-tensor-pullback-normalization).

Proof: inverse image preserves K-flat complexes. The hypothesis hc computes c
on the given complex P by the ordinary scalar/pullback comparison. The defining
equation of scalarTensorIso computes both scalar/tensor comparisons using the
ordinary balancing map m tensor b -> b tensor m. This map is an isomorphism:
its inverse is b tensor m -> m tensor b, and the balancing relations make these
maps well-defined before sheafification. Both descend through sheafification.
The defining counit square of leftDerivedUpperStarTensorComparison computes its
value on P and the coefficient sheaf in degree zero. The exact restriction/pullback
square is computed termwise. Substitute these representative equations into hc
after applying exact restriction. The ordinary comparisons in the resulting two
composites agree: on a pulled-back pure tensor m tensor b both retain m and b;
the coefficient-unit identification sends the pulled-back unit to the unit.
Indeed the conjugate scalar/pullback comparison preserves the composite
adjunction units by its defining Hom-equivalence equation. The restriction/pullback
comparison has the same unit normalization, by the two adjunction triangle
identities. These equations identify their values on the pullback generators.
This can be checked before sheafification and then degreewise on complexes.
There is no interchange of complex degrees, so no sign occurs. The tensorator
of Q with K-flat first factor P (and likewise its inverse image) is invertible,
as are the geometric representative counits and the ordinary balancing maps.
Cancel their images to obtain the displayed equality at Q(P). No flatness of
B over A is used, since the K-flat factor is P. -/
theorem scalarTensorPullback_normalization_kFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (c : L(upperStar (ModuleCat.{u + 1} B) f).obj
        ((scalarExtension φ W).obj (_root_.DerivedCategory.Q.obj P)) ⟶
      (scalarExtension φ Z).obj
        (L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P)))
    (hc :
      c ≫
          (scalarExtension φ Z).map
            ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Qh.map
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P)) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctorCounit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj
                (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P)) ≫
            _root_.DerivedCategory.Qh.map
              (((upperStar (ModuleCat.{u + 1} B) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app
                (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P))) ≫
          _root_.DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
                ((conjugateIsoEquiv
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
                    (ProEtale.etaleSheafExtendScalarsAdjunction φ Z))
                  ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).comp
                    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
                  (lowerStarCompRestrictScalarsIso φ f).symm) (.up ℤ) ≪≫
              (Functor.mapHomologicalComplexCompIso
                (Iso.refl (upperStar (ModuleCat.{u + 1} A) f ⋙
                  ProEtale.etaleSheafExtendScalars φ Z)) (.up ℤ)).symm).hom.app P))
    :
    let C := _root_.DerivedCategory.Q.obj P
    (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ W).obj C) ≫
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map c ≫
        (scalarTensorIso φ Z).hom.app (L(upperStar (ModuleCat.{u + 1} A) f).obj C) =
      L(upperStar (ModuleCat.{u + 1} A) f).map ((scalarTensorIso φ W).hom.app C) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app C).app
          (scalarCoefficient φ W) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (L(upperStar (ModuleCat.{u + 1} A) f).obj C)).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app _ ≪≫
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
            (_root_.DerivedCategory.singleFunctor _ 0).mapIso
              ((upperStarRestrictScalarsIsoSheaf φ f).app (𝟙_ _) ≪≫
                (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
                  (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm)).hom := by
  sorry

end AlgebraicGeometry.Etale
