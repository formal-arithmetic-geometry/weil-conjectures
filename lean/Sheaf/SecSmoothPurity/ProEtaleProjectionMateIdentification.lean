/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.Paper.RingedCoefficientProjectionCocycle
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Identification of the normalized pro-etale coefficient projection mate

Source: Stacks Project, sites-cohomology.tex, Tags 07A7 and 07A6;
sites-modules.tex, Tags 03D3 and 03EL
(blueprint: lem-sp-proetale-projection-mate-identification).

All operations below specialize the recorded ordinary unbounded operations.
The comparison witnesses are constrained by ordinary sections, localization
computation maps, and the actual adjunction bijections. The theorem asserts their
unique existence together with the equality of the two prescribed mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [instance 200000] SheafOfModules.instAbelian
  essentiallySmall_of_small_of_locallySmall

attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale.ProjectionMateIdentification

/-- Literal inverse-image coefficients, without constant-ring identification.
Source: Stacks 07A7 (blueprint: lem-sp-proetale-projection-mate-identification). -/
abbrev inverseRing {X Y : Scheme.{u}} (q : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R

/-- The literal geometric module pullback, using the identity structural map.
Source: Stacks 03D3 (blueprint: lem-sp-proetale-projection-mate-identification). -/
abbrev literalPull {X Y : Scheme.{u}} (q : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  proEtaleRingModulePullback q R (inverseRing q R) (Iso.refl _)

/-- The literal derived geometric adjunction, including its prescribed counit.
Source: Stacks 07A6 (blueprint: lem-sp-proetale-projection-mate-identification). -/
abbrev literalAdj {X Y : Scheme.{u}} (q : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedAdjunction q R (inverseRing q R) (Iso.refl _)

/-- The literal geometric direct image on the entire unbounded category.
Source: Stacks 07A6 (blueprint: lem-sp-proetale-projection-mate-identification). -/
abbrev literalPush {X Y : Scheme.{u}} (q : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedDirectImage q R (inverseRing q R) (Iso.refl _)

/-- Change action through the canonical constant-section ring comparison.
Its inverse changes action through the inverse of that very comparison.
Source: Stacks 03D3, 0H7J (blueprint: lem-sp-proetale-projection-mate-identification). -/
abbrev restrict {X Y : Scheme.{u}} (q : X ⟶ Y) (A : Type u) [CommRing A] :=
  proEtaleRingRestrictScalars (proEtaleConstantRingComparison q A).hom

/-- The actual inverse image of the given coefficient map.
Source: Stacks 07A7 (blueprint: lem-sp-proetale-projection-mate-identification). -/
abbrev inverseMap {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (φ : A →+* B) :=
  (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
    (proEtaleConstantRingMap (T := Y) φ)

/-- The canonical literal inverse-image/tensor comparison, with identity structural maps.
Source: Stacks 03EL, 06YY (blueprint: lem-sp-proetale-projection-mate-identification). -/
def literalTensor {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (φ : A →+* B) :=
  proEtaleReductionPullbackIso q (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (inverseRing q (proEtaleConstantRing Y A)) (inverseRing q (proEtaleConstantRing Y B))
    (proEtaleConstantRingMap (T := Y) φ) (inverseMap q φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- The literal ringed-topos coefficient projection: precisely the counit mate.
This is the specialization of RingedCoefficientProjection.comparison to the
recorded geometric adjunctions and scalar extensions, with its same mate convention.
Source: Stacks 07A7 (blueprint: lem-sp-proetale-projection-mate-identification). -/
def literalMate {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (φ : A →+* B) :=
  (mateEquiv (literalAdj q (proEtaleConstantRing Y A))
    (literalAdj q (proEtaleConstantRing Y B)) (literalTensor q φ).hom).natTrans

/-- A normalized change from literal coefficients to constant coefficients.
The ordinary comparison preserves every geometric unit section; the derived
right comparison preserves the actual adjunction bijection, hence its counit.
Source: Stacks 03D3, 07A6, 0D6D, 0D6E
(blueprint: lem-sp-proetale-projection-mate-identification). -/
def RingTransport {X Y : Scheme.{u}} (q : X ⟶ Y)
    (A : Type u) [CommRing A] :=
  Σ' ordinary : literalPull q (proEtaleConstantRing Y A) ≅
    proEtaleConstantRingPullback A q ⋙ restrict q A,
  Σ' direct : directImageConstantPush A q ≅
    (restrict q A).mapDerivedCategory.{u + 2, u + 2} ⋙ literalPush q (proEtaleConstantRing Y A),
  (∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (U : Y.ProEtᵒᵖ) (m : M.val.obj U),
    (ordinary.hom.app M).val.app ((proEtaleBaseChange q).op.obj U)
      (((proEtaleRingModuleAdjunction q (proEtaleConstantRing Y A)
        (inverseRing q (proEtaleConstantRing Y A)) (Iso.refl _)).unit.app M).val.app U m) =
      ((proEtaleConstantRingAdjunction A q).unit.app M).val.app U m) ∧
  (∀ (M : proEtaleDerivedCategory Y A) (N : proEtaleDerivedCategory X A)
    (t : (proEtaleConstantRingDerivedPullback A q).obj M ⟶ N),
    (literalAdj q (proEtaleConstantRing Y A)).homEquiv _ _
      (((mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2} ordinary ≪≫
        mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1,
          u + 1, u + 1, u + 2, u + 2, u + 2}
          (proEtaleConstantRingPullback A q) (restrict q A)).hom.app M)
          ≫ (restrict q A).mapDerivedCategory.{u + 2, u + 2}.map t) =
      (directImageConstantAdjunction A q).homEquiv M N t ≫ direct.hom.app N)

/-- The normalized ordinary transport, projected from its full normalization data.
Source: Stacks 03D3 (blueprint: lem-sp-proetale-projection-mate-identification). -/
def RingTransport.ordinary {X Y : Scheme.{u}} {q : X ⟶ Y}
    {A : Type u} [CommRing A] (t : RingTransport q A) := t.1

/-- The normalized derived direct-image transport, retaining the specified adjunction.
Source: Stacks 07A6 (blueprint: lem-sp-proetale-projection-mate-identification). -/
def RingTransport.direct {X Y : Scheme.{u}} {q : X ⟶ Y}
    {A : Type u} [CommRing A] (t : RingTransport q A) := t.2.1

/-- The exact termwise descent of the section-normalized ordinary comparison.
Source: Stacks 0D6D (blueprint: lem-sp-proetale-projection-mate-identification). -/
def RingTransport.pullback {X Y : Scheme.{u}} {q : X ⟶ Y}
    {A : Type u} [CommRing A] (t : RingTransport q A) :=
  mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2} t.ordinary ≪≫
    mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1,
          u + 1, u + 1, u + 2, u + 2, u + 2}
          (proEtaleConstantRingPullback A q) (restrict q A)

/-- The ordinary scalar-coordinate comparison, with its unique pure-tensor formula,
and the derived comparison fixed on all flat-term K-flat representatives.
Source: Stacks 03EL, 06YY (blueprint: lem-sp-proetale-projection-mate-identification). -/
def ScalarTransport {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (φ : A →+* B) :=
  Σ' ordinary : proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ) ⋙ restrict q B ≅
    restrict q A ⋙ proEtaleRingExtension (inverseMap q φ),
  Σ' derived : scalarExtensionFunctor φ X ⋙ (restrict q B).mapDerivedCategory.{u + 2, u + 2} ≅
    (restrict q A).mapDerivedCategory.{u + 2, u + 2} ⋙
      proEtaleRingDerivedExtension (inverseMap q φ),
  (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (b : (inverseRing q (proEtaleConstantRing Y B)).obj.obj U) (m : M.val.obj U),
    (ordinary.hom.app M).val.app U
      (reductionTensorSection X (proEtaleConstantRingMap (T := X) φ) M U
        ((proEtaleConstantRingComparison q B).hom.hom.app U b) m) =
      reductionTensorSection X (inverseMap q φ) ((restrict q A).obj M) U b m) ∧
  (∀ (P : CochainComplex
      (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := proEtaleConstantRing X A) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := proEtaleConstantRing X A) (P.X n)) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        (proEtaleRingDerivedExtension (inverseMap q φ)).map
          ((restrict q A).mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app P) ≫
        reductionScalarComplexCounit X (inverseMap q φ)
          (((restrict q A).mapHomologicalComplex (.up ℤ)).obj P) =
      (restrict q B).mapDerivedCategory.{u + 2, u + 2}.map (scalarExtensionFunctorCounit φ X P) ≫
        (restrict q B).mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app
          (((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

/-- The balanced ordinary coefficient-coordinate transport, with its pure-tensor formula.
Source: Stacks 03EL (blueprint: lem-sp-proetale-projection-mate-identification). -/
def ScalarTransport.ordinary {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} {q : X ⟶ Y} {φ : A →+* B} (t : ScalarTransport q φ) := t.1

/-- The derived coefficient-coordinate transport fixed by its representative square.
Source: Stacks 06YY (blueprint: lem-sp-proetale-projection-mate-identification). -/
def ScalarTransport.derived {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} {q : X ⟶ Y} {φ : A →+* B} (t : ScalarTransport q φ) := t.2.1

/-- A representative characterization of a specified tensor/pullback comparison.
The ordinary pure-tensor identity fixes every scalar, not only the tensor unit.
The representative square uses the universal scalar counits and exact geometric descent.
Source: Stacks 03EL, 06YY, 0G7E
(blueprint: lem-sp-proetale-projection-mate-identification). -/
def TensorModel {X Y : Scheme.{u}} (q : X ⟶ Y)
    (R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R' S' : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : R ⟶ S) (a' : R' ⟶ S')
    (cR : inverseRing q R ≅ R') (cS : inverseRing q S ≅ S')
    (α : proEtaleRingDerivedExtension a ⋙ proEtaleRingDerivedPullback q S S' cS ≅
      proEtaleRingDerivedPullback q R R' cR ⋙ proEtaleRingDerivedExtension a') : Prop :=
  ∃ ordinary : proEtaleRingExtension a ⋙ proEtaleRingModulePullback q S S' cS ≅
    proEtaleRingModulePullback q R R' cR ⋙ proEtaleRingExtension a',
  (∀ (M : proEtaleRingModules Y R) (U : Y.ProEtᵒᵖ)
    (b : S.obj.obj U) (m : M.val.obj U),
    (ordinary.hom.app M).val.app ((proEtaleBaseChange q).op.obj U)
      (((proEtaleRingModuleAdjunction q S S' cS).unit.app
        ((proEtaleRingExtension a).obj M)).val.app U
          (reductionTensorSection Y a M U b m)) =
      reductionTensorSection X a' ((proEtaleRingModulePullback q R R' cR).obj M)
        ((proEtaleBaseChange q).op.obj U)
        ((proEtaleRingDirectImageMap q S S' cS).hom.app U b)
        (((proEtaleRingModuleAdjunction q R R' cR).unit.app M).val.app U m)) ∧
  (∀ (P : CochainComplex (proEtaleRingModules Y R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) (P.X n)) →
    α.hom.app (DerivedCategory.Q.obj P) ≫
        (proEtaleRingDerivedExtension a').map
          ((proEtaleRingModulePullback q R R' cR).mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app
            P) ≫
        reductionScalarComplexCounit X a'
          (((proEtaleRingModulePullback q R R' cR).mapHomologicalComplex (.up ℤ)).obj P) =
      (proEtaleRingDerivedPullback q S S' cS).map (reductionScalarComplexCounit Y a P) ≫
        (proEtaleRingModulePullback q S S' cS).mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app
          (((proEtaleRingExtension a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P))

/-- All identifications of the two coefficient presentations. Each coordinate map is
fixed by sections or by its universal localization computation, and direct images
are fixed by the prescribed adjunction bijection, including its counit.
Source: Stacks 07A7 (blueprint: lem-sp-proetale-projection-mate-identification). -/
structure Data {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (φ : A →+* B) where
  ringA : RingTransport q A
  ringB : RingTransport q B
  scalar : ScalarTransport q φ
  literalModel : TensorModel q (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (inverseRing q (proEtaleConstantRing Y A)) (inverseRing q (proEtaleConstantRing Y B))
    (proEtaleConstantRingMap (T := Y) φ) (inverseMap q φ)
    (Iso.refl _) (Iso.refl _) (literalTensor q φ)
  constantModel : TensorModel q (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison q A) (proEtaleConstantRingComparison q B)
    (directImageScalarPullbackIso φ q)

/-- Equality of the tensor maps and of their counit mates in the literal B-coordinates.
Restriction through c_B is an equivalence, so these are precisely equality of the
transported natural transformations in the constant B-coordinates. All functors in
these equations are the fixed constructions, with no freely chosen adjunction.
Source: Stacks 07A7 (blueprint: lem-sp-proetale-projection-mate-identification). -/
def Data.Identifies {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} {q : X ⟶ Y} {φ : A →+* B} (d : Data q φ) : Prop :=
  (∀ K : proEtaleDerivedCategory Y A,
    (literalTensor q φ).hom.app K ≫
        (proEtaleRingDerivedExtension (inverseMap q φ)).map (d.ringA.pullback.hom.app K) ≫
        d.scalar.derived.inv.app ((proEtaleConstantRingDerivedPullback A q).obj K) =
      d.ringB.pullback.hom.app ((scalarExtensionFunctor φ Y).obj K) ≫
        (restrict q B).mapDerivedCategory.{u + 2, u + 2}.map
          ((directImageScalarPullbackIso φ q).hom.app K)) ∧
  (∀ E : proEtaleDerivedCategory X A,
    (scalarExtensionFunctor φ Y).map (d.ringA.direct.hom.app E) ≫
        (literalMate q φ).app ((restrict q A).mapDerivedCategory.{u + 2, u + 2}.obj E) ≫
        (literalPush q (proEtaleConstantRing Y B)).map (d.scalar.derived.inv.app E) =
      (directImageScalarComparison φ q).app E ≫
        d.ringB.direct.hom.app ((scalarExtensionFunctor φ X).obj E))

/-- The prescribed pro-etale scalar/direct-image map is exactly the literal ringed-topos
mate transported through the canonical constant-section ring comparisons. All
comparisons are uniquely normalized, on the entire unbounded categories.
Source: Stacks Project, sites-cohomology.tex, Tag 07A7 (remark-base-change);
Tags 07A6, 0D6D, 0D6E, 06YY, 0G7E and sites-modules.tex Tags 03D3, 03EL
(blueprint: lem-sp-proetale-projection-mate-identification).

Proof:
1. The canonical constant-ring comparisons are invertible and commute with phi:
   take adjuncts, where both maps send a constant a to the constant phi(a).
2. Restriction through c_R changes only the action. Its inverse uses c_R inverse.
   The ordinary tensor comparison m tensor r maps to c_R inverse(r)m, with inverse
   m mapping to m tensor 1. Balancing and restriction compatibility give the
   section-normalized ordinary geometric comparison, uniquely.
3. On K-injectives the literal and ringed derived Hom bijections are the ordinary
   termwise bijection: inverse image is exact, so direct image preserves
   K-injectives. Use the K-injective Hom theorem and the representing-fraction
   formula of preDerivedAdjunctionGeneral to identify the canonical bijections.
4. proEtaleRingSheafChangeAdjunction identifies these with the constant-coefficient
   bijections. Apply its adjunct equation at the counit to obtain the exact
   counit normalization. Thus the RingTransport direct comparison is unique.
5. The ordinary inverse-image tensor comparison of
   inverseImage_tensor_comparison sends the inverse image of x tensor b to
   inverse image x tensor inverse image b. The coefficient square in step 1
   identifies actions. Balancing gives the ScalarTransport pure formula and
   both TensorModel pure formulas, with the same constant b.
6. Resolve an arbitrary complex by a flat-term K-flat complex. Geometric and
   scalar pullbacks preserve that class by isKFlat_ringedToposPullback.
   The scalar counits and exact factorization maps give the representative
   squares. Their ordinary maps agree by step 5. K-flat localization via
   site_derived_tensor_descent_independentCoefficients gives the unique derived
   comparisons and the first equality in Identifies.
7. Both prescribed mates now have adjunct T_X(epsilon_A) after lambda. The two
   triangle identities show the adjunction bijection is invertible. Hence their
   components, and thus their natural transformations, agree. This gives the
   second equality in Identifies and the displayed unique counit-transpose
   characterization. Naturality is built into every comparison. No flatness,
   boundedness, properness, or invertibility of the direct-image map is used. -/
theorem proEtale_projection_mate_identification
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0) (_hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (φ : A →+* B) {X Y : Scheme.{u}} (q : X ⟶ Y) :
    (∃! d : Data q φ, d.Identifies) ∧
    ∀ E : proEtaleDerivedCategory X A,
      ∀ k : (scalarExtensionFunctor φ Y).obj ((directImageConstantPush A q).obj E) ⟶
          (directImageConstantPush B q).obj ((scalarExtensionFunctor φ X).obj E),
        (proEtaleConstantRingDerivedPullback B q).map k ≫
            (directImageConstantAdjunction B q).counit.app ((scalarExtensionFunctor φ X).obj E) =
          (directImageScalarPullbackIso φ q).hom.app ((directImageConstantPush A q).obj E) ≫
            (scalarExtensionFunctor φ X).map ((directImageConstantAdjunction A q).counit.app E) ↔
          k = (directImageScalarComparison φ q).app E :=
  sorry

end AlgebraicGeometry.ProEtale.ProjectionMateIdentification
