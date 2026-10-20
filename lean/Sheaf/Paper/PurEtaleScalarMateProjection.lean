/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q158
-/
module

public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import Sheaf.Paper.PbcActualScalarPullback
public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Restriction of the derived coefficient mate equals the projection morphism

Source: Stacks Project, more-etale.tex, Tag 0GL6, with the canonical counit calculation
in sites-cohomology.tex, Tags 07A4, 0G7E and 07A7
(blueprint: lem-pur-etale-scalar-mate-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary scalar/pullback identification, conjugate to the sectionwise
restriction/direct-image identity under the two composite adjunctions.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarSheafPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ProEtale.etaleSheafExtendScalars φ W ⋙ upperStar (ModuleCat.{u + 1} B) f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ProEtale.etaleSheafExtendScalars φ Z :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ Z))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))).symm
    (lowerStarCompRestrictScalarsIso φ f).symm

/-- The same comparison on actual cochain complexes.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarSheafPullbackComplexIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :=
  Functor.mapHomologicalComplexCompIso (scalarSheafPullbackIso φ f) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (upperStar (ModuleCat.{u + 1} A) f ⋙
        ProEtale.etaleSheafExtendScalars φ Z)) (.up ℤ)).symm

/-- The geometric derived counit, with the homotopy quotient comparison included.
Source: Stacks 07A4 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarGeometricRepresentative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    _root_.DerivedCategory.Qh.map
      (((upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P)

/-- The canonical scalar/pullback comparison is uniquely normalized on K-flat models.
Source: Stacks 07A4, 0G7E and 07A7
(blueprint: lem-pur-etale-scalar-mate-projection).
Proof: resolve the input by a K-flat complex with flat terms (lem-pc-kflat-resolution).
Inverse image preserves those properties by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback; scalar extension is termwise
extension on these models by lem-pur-derived-change-of-rings. Apply the ordinary
scalar/pullback isomorphism termwise. The derived counits give the displayed square.
Naturality and invariance under quasi-isomorphisms descend it to derived categories.
Every object has such a model and the vertical counits on these models are invertible,
so the displayed equations determine the natural isomorphism uniquely. -/
theorem scalarPullbackIso_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ∃! c : scalarExtension φ W ⋙ L(upperStar (ModuleCat.{u + 1} B) f) ≅
        L(upperStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ Z,
      ∀ (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      c.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (scalarExtension φ Z).map (scalarGeometricRepresentative A f P) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          scalarGeometricRepresentative B f
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P) := by
  sorry

/-- The uniquely normalized derived scalar/pullback isomorphism.
Source: Stacks 07A4 and 0G7E (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    scalarExtension φ W ⋙ L(upperStar (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ Z :=
  (scalarPullbackIso_existsUnique φ f).choose

/-- The B-linear scalar-change mate; its components are precisely the transposes
of the scalar extension of the A-geometric counit after scalarPullbackIso.
Source: Stacks 0GL6 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    R(lowerStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ W ⟶
      scalarExtension φ Z ⋙ R(lowerStar (ModuleCat.{u + 1} B) f) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom)).natTrans

/-- The specified identification f_A^{-1}B_W[0] = B_Z[0].
Source: Stacks 07A4 and 07A6 (blueprint: lem-pur-etale-scalar-mate-projection). -/
def scalarCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj (scalarCoefficient φ W) ≅
      scalarCoefficient φ Z :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((upperStarRestrictScalarsIsoSheaf φ f).app (𝟙_ _) ≪≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm)

/-- After canonical scalar/tensor and restriction/direct-image identifications,
the coefficient mate is the specified projection morphism, naturally in J.
Source: Stacks more-etale.tex 0GL6; sites-cohomology.tex 07A4, 0G7E and 07A7
(blueprint: lem-pur-etale-scalar-mate-projection).

Proof: (1) scalarTensorIso is natural on morphisms, since on K-flat models it is
the ordinary balancing map of lem-pur-change-of-rings-tensor-comparison; use
lem-pc-kflat-resolution and lem-pur-derived-change-of-rings to descend it.
(2) On these same models the restriction of scalarPullbackIso is exactly the
inverse monoidal comparison used in def-kun-projection-formula-map, by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback: both maps retain the tensor and
pull back its first factor. (3) Take the A-adjoint transpose of the restricted
B-mate. The counit identity of lem-sbc-restrict-scalars-derived-adjunction-identities
and naturality of scalarRestrictionPullbackIso identify it with restriction of
the scalar-extended A-counit. The supplied bounds ensure every comparison from
lem-sbc-canonical-restrict-scalars-functor-comparisons is used on D+; the adjunctions
are the same restrictions of those in sbc-def-base-change-map and
def-kun-unbounded-exchange. (4) Conjugate by scalarTensorIso on source and target.
Its naturality and (2) give exactly the transpose defining the projection morphism
of def-kun-projection-formula-map. Injectivity of the A-adjunction Hom equivalence
gives the asserted equality. All maps are natural transformations, so this is an
equality natural in J on the full subcategory satisfying the three bounds. -/
theorem scalarMate_restrict_eq_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (J : _root_.DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hN : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ Z).obj J.obj)
    (_hM : ∃ M : _root_.DerivedCategory.Plus
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)),
      M.obj = (scalarExtension φ W).obj
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj J.obj)) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).map
        ((scalarMate φ f).app J.obj) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ Z).obj J.obj) =
      (scalarTensorIso φ W).hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj J.obj) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J.obj).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj J.obj).map
              (scalarCoefficientPullbackIso φ f).hom ≫
            (scalarTensorIso φ Z).inv.app J.obj) := by
  sorry

end AlgebraicGeometry.Etale
