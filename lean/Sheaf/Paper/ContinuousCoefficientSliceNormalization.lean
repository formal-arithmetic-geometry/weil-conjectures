/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.UnramifiedMorphism

/-! # Normalized continuous coefficient restriction to a pro-etale slice

Source: Bhatt--Scholze, Definition 6.8.1, Lemma 6.8.2, paragraph before Definition
6.8.6 and Remark 6.8.15; Stacks, Tags 00VC, 00XZ, 03EL, 06YY and 0G7E
(blueprint: lem-per-continuous-coefficient-slice-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ContinuousSlice

/-- Literal module restriction along composition with a site object. The scalar ring
is the literal restriction of R; both sections and morphisms are precomposed.
Source: Stacks 00XZ and 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def modules {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcModules X R ⥤ pbcModules U.left
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) :=
  letI : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  SheafOfModules.pushforward (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology X) (𝟙 _)

/-- Exactness of literal restriction, including nonnoetherian U.
Source: Stacks 00XZ, 03EL and 03CZ
(blueprint: lem-per-continuous-coefficient-slice-normalization).
Proof: identify the sites using weaklyEtale_localization. Restriction is module
inverse image over the inverse-image ring by proEtaleObjectInverseImageRestriction.
Apply localization_inverseImage_exact. No coefficient flatness, boundedness or
noetherian hypothesis on the object is used. -/
theorem modules_exact {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (modules U R).Additive ∧ PreservesFiniteLimits (modules U R) ∧
      PreservesFiniteColimits (modules U R) := sorry

/-- The additive structure supplied by exact restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_additive {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : (modules U R).Additive :=
  (modules_exact U R).1

/-- Finite limits preserved by restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_limits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (modules U R) := (modules_exact U R).2.1

/-- Finite colimits preserved by restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_colimits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (modules U R) := (modules_exact U R).2.2

/-- Unbounded derived restriction is exact termwise restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def derived {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (modules U R).mapDerivedCategory

/-- The coefficient identification is the identity on continuous functions on V.
Source: Bhatt--Scholze 6.8.1; Stacks 00XZ
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def ring {X : Scheme.{u}} (U : X.ProEt) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      U.hom U.prop).obj (continuousCoefficientSheaf X T) ≅
      continuousCoefficientSheaf U.left T :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- Actual inverse image is normalized by its Kan coprojections and sheafification
unit, and its coefficient structural map becomes the identity on the same V.
Source: Bhatt--Scholze 6.8.1; Stacks 00VC and 00XZ
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Coefficients {X : Scheme.{u}} (U : X.ProEt) where
  sets : ProEtaleObjectRestrictionComparison U (Type (u + 1))
  groups : ProEtaleObjectRestrictionComparison U AddCommGrpCat.{u + 1}
  rings : ProEtaleObjectRestrictionComparison U RingCat.{u + 1}
  commRings : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}
  initial : ∀ V : U.left.ProEt,
    Nonempty (IsInitial (proEtaleObjectInverseImageIndexPoint U V))
  continuous : ∀ (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T],
    IsIso (continuousCoefficientPullback T U.hom) ∧
      continuousCoefficientPullback T U.hom =
        commRings.sheafIso.hom.app (continuousCoefficientSheaf X T) ≫ (ring U T).hom
  constants : ∀ (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] (V : U.left.ProEt) (a : T),
    (ring U T).hom.hom.app (op V)
      (ContinuousMap.const V.left a) = ContinuousMap.const V.left a
  coefficient_maps : ∀ (T S : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
      (h : T →+* S) (hc : Continuous h),
    (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).map
        (continuousCoefficientMap h hc X) ≫ continuousCoefficientPullback S U.hom =
      continuousCoefficientPullback T U.hom ≫ continuousCoefficientMap h hc U.left
  finite : ∀ (A : CommRingCat.{u + 1}) [Finite A],
    IsIso (proEtaleConstantInverseImageMap U.hom CommRingCat.{u + 1} A)

/-- The residue projections to the actual finite constant sheaves, using the canonical
constant-function comparison, not an arbitrary identification of the quotient.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def residue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    integralCoefficientSheaf l X E ⟶ (finiteCoefficientTower l X E).obj (op n) :=
  continuousCoefficientReduction l E X n ≫ (discreteContinuousCoefficientIso X).inv.app
    (finiteCoefficientRing l E n)

/-- Coefficient and quotient normalization, retaining every positive level n+1.
The finite structural maps are the constant-section maps of the actual inverse image.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Adic (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}} (g : Y ⟶ X) where
  integral : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (integralCoefficientSheaf l X E) ≅ integralCoefficientSheaf l Y E
  rational : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (rationalCoefficientSheaf l X E) ≅ rationalCoefficientSheaf l Y E
  integral_normalized : integralCoefficientRestrictionNormalized l E g integral.hom
  rational_normalized : rationalCoefficientRestrictionNormalized l E g rational.hom
  quotient : ∀ n : ℕ,
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      ((finiteCoefficientTower l X E).obj (op n)) ≅
        (finiteCoefficientTower l Y E).obj (op n)
  quotient_constants : ∀ n : ℕ, (quotient n).hom =
    proEtaleCoefficientInverseImageMap g (Padic.coefficientExtensionRing l E (n + 1))
  transitions : ∀ (m n : ℕ) (h : n ≤ m),
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (finiteCoefficientRingMap l E h)) ≫ (quotient n).hom =
      (quotient m).hom ≫ (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E h)
  projections : ∀ n : ℕ,
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (residue l E X n) ≫
        (quotient n).hom = integral.hom ≫ residue l E Y n
  inclusion : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (integralRationalCoefficientMap l E X) ≫ rational.hom =
    integral.hom ≫ integralRationalCoefficientMap l E Y

/-- The completed and localized coefficient identifications with their canonical projections.
Source: Bhatt--Scholze 6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Completion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) where
  integral : integralCoefficientSheaf l X E ≅ finiteCoefficientLimit l X E
  projections : ∀ n : ℕ,
    integral.hom ≫ limit.π (finiteCoefficientTower l X E) (op n) = residue l E X n
  rational : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E
  fractions : integralCoefficientLocalizationNormalized l E X rational.hom

/-- Finite-quotient normalization of the completed structural map.
Source: Bhatt--Scholze 6.8.2 and Remark 6.8.15
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure CompletedPull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (a : Adic l E g) (bX : Completion l E X) (bY : Completion l E Y) where
  integral : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (finiteCoefficientLimit l X E) ≅ finiteCoefficientLimit l Y E
  normalization : integral.hom =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map bX.integral.inv ≫
      a.integral.hom ≫ bY.integral.hom
  projections : ∀ n : ℕ,
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (limit.π (finiteCoefficientTower l X E) (op n)) ≫ (a.quotient n).hom =
      integral.hom ≫ limit.π (finiteCoefficientTower l Y E) (op n)

/-- Ring-isomorphism scalar extension has exact ordinary inverse image as its derived
functor, normalized by the scalar-extension counit on every complex.
Source: Stacks 03EL, 03CZ and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure ExactPull {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) where
  scalar : pbcExtend c.hom ≅ pbcRestrict c.inv
  scalar_sections : ∀ (M : pbcModules Y
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
      (V : Y.ProEtᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
    (scalar.hom.app M).val.app V (pbcTensorSection c.hom M V s m) =
      (c.inv.hom.app V s) • m
  scalar_complex : (pbcExtend c.hom).mapHomologicalComplex (.up ℤ) ≅
    (pbcRestrict c.inv).mapHomologicalComplex (.up ℤ)
  scalar_complex_components : ∀ P (n : ℤ),
    (scalar_complex.hom.app P).f n = scalar.hom.app (P.X n)
  scalar_derived : pbcDerivedExtend c.hom ≅ (pbcRestrict c.inv).mapDerivedCategory
  scalar_normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    pbcComplexCounit c.hom P ≫ DerivedCategory.Q.map (scalar_complex.hom.app P) =
      scalar_derived.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcRestrict c.inv).mapDerivedCategoryFactors.hom.app P
  [limits : PreservesFiniteLimits (pbcExtend c.hom)]
  ordinary : proEtaleModuleInverseImage f R ⋙ pbcExtend c.hom ≅
    proEtaleRingModulePullback f R S c
  derived : adicTowerPullback f R ⋙ pbcDerivedExtend c.hom ≅
    proEtaleRingDerivedPullback f R S c
  normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    IsIso (pbcComplexCounit c.hom P)

/-- Normalized module restriction for a coefficient ring, with exact termwise derived
restriction and the canonical unit formula on the same underlying object.
Source: Stacks 03EL and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure ModuleComparison {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (b : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) where
  ordinary : proEtaleRingModulePullback U.hom R
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) (b.sheafIso.app R) ≅ modules U R
  unit : ∀ (M : pbcModules X R) (V : X.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange U.hom).obj V))
      (proEtaleRingModuleUnitSection U.hom R _ (b.sheafIso.app R) M V m) =
        M.val.map (MorphismProperty.Over.homMk
          (pullback.fst V.hom U.hom) pullback.condition).op m
  complex :
    (proEtaleRingModulePullback U.hom R
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) (b.sheafIso.app R)).mapHomologicalComplex (.up ℤ) ≅
      (modules U R).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  derived : proEtaleRingDerivedPullback U.hom R
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) (b.sheafIso.app R) ≅ ContinuousSlice.derived U R
  normalization : ∀ P : CochainComplex (pbcModules X R) ℤ,
    (proEtaleRingDerivedPullbackFactors U.hom R _ (b.sheafIso.app R)).hom.app P ≫
        DerivedCategory.Q.map
          (complex.hom.app P) =
      derived.hom.app (DerivedCategory.Q.obj P) ≫
        (modules U R).mapDerivedCategoryFactors.hom.app P

/-- Restricting an ambient derived tensor pullback is scalar extension on the restricted
inverse image. The counit equation specifies the comparison on K-flat representatives.
Source: Stacks 03EL, 06YS, 0G7E and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Ambient {X Y : Scheme.{u}} (f : Y ⟶ X) (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S) where
  ordinary : pbcExtend c ⋙ modules U S ≅
    modules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⋙
      pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).map c)
  sections : ∀ (M : pbcModules Y
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
      (V : U.left.ProEtᵒᵖ) (s : S.obj.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
      (m : M.val.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))),
    (ordinary.hom.app M).val.app V (pbcTensorSection c M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) s m) =
      pbcTensorSection ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c) ((modules U _).obj M) V s m
  complex : (pbcExtend c).mapHomologicalComplex (.up ℤ) ⋙
      (modules U S).mapHomologicalComplex (.up ℤ) ≅
    (modules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).mapHomologicalComplex
      (.up ℤ) ⋙
      (pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  scalar_derived : pbcDerivedExtend c ⋙ ContinuousSlice.derived U S ≅
    ContinuousSlice.derived U
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⋙
      pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)
  normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    (ContinuousSlice.derived U S).map (pbcComplexCounit c P) ≫
        (modules U S).mapDerivedCategoryFactors.hom.app
          (((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      scalar_derived.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)).map
          ((modules U _).mapDerivedCategoryFactors.hom.app P) ≫
        pbcComplexCounit ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)
          (((modules U _).mapHomologicalComplex (.up ℤ)).obj P)

/-- The ambient formula after the actual geometric inverse image. This is obtained by
whiskering the counit-normalized scalar comparison, so it is fixed on representatives.
Source: Stacks 06YY and 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def Ambient.pullback {X Y : Scheme.{u}} {f : Y ⟶ X} {U : Y.ProEt}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S}
    (a : Ambient f U R S c) :=
  Functor.isoWhiskerLeft (adicTowerPullback f R) a.scalar_derived

/-- The complete slice normalization assertion. Geometric finiteness hypotheses are
used only for identifying completed coefficients and for the etale/immersion corollary.
Source: Bhatt--Scholze 6.8.1, 6.8.2, 6.8.6 and 6.8.15
(blueprint: lem-per-continuous-coefficient-slice-normalization).

Proof, following all seven steps of the node:
1. weaklyEtale_localization identifies coverings and literal restriction; U need not
be noetherian. 2. proEtaleObjectInverseImageRestriction identifies the distinguished
initial index and the Kan coprojection, and its sheafification unit is invertible.
3. At that index continuousCoefficientPullback is identity on functions. Postcomposition
commutes with precomposition, preserving A to E, residues and constants. The finite
constant-section theorem identifies residue sheaves; uniqueness gives every transition.
4. The normalized completion and localization comparisons identify B_X and B_X[1/varpi]
with A_X and E_X. The projections restrict sectionwise, not by a general assertion that
inverse image commutes with infinite limits. 5. localization_inverseImage_exact gives
exactness. For an isomorphism c, b tensor m maps to c inverse(b)m, inverse m maps to
1 tensor m, so scalar extension is exact and all complexes compute its derived functor.
6. An etale map is weakly etale (its diagonal is open, hence flat); use the slice result.
For an immersion use continuousCoefficientImmersionRestriction instead.
7. Resolve by flat-term K-flat complexes. KFlatRingedToposPullback preserves these under
inverse image and restriction. LocalizedSiteTensorRestriction sends each sheafified pure
tensor to the identical tensor, so its degreewise maps commute with differentials and
coefficient maps. RingedTopoiDerivedPullback makes the derived comparison independent of
the chosen resolution. Apply this for both the integral and rational rings. -/
theorem continuous_coefficient_slice_normalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ (X : Scheme.{u}) (U : X.ProEt), ∃ b : Coefficients U,
      ∃ a : Adic l E U.hom,
      Nonempty (ExactPull U.hom _ _ a.integral) ∧
      Nonempty (ExactPull U.hom _ _ a.rational) ∧
      ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
        Nonempty (ModuleComparison U R b.commRings)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X]
      (_hd : ∃ n : ℕ, topologicalKrullDim X ≤ n)
      (_hi : ∀ x : X, IsUnit (l : X.presheaf.stalk x)),
      Nonempty (Completion l E X)) ∧
    (∀ (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
      (_hdX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
      (_hdY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
      (_hiX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
      (_hiY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (g : Y ⟶ X),
      (Etale g ∨ IsImmersion g) →
      ∃ a : Adic l E g,
        Nonempty (ExactPull g _ _ a.integral) ∧
        Nonempty (ExactPull g _ _ a.rational) ∧
        ∀ (bX : Completion l E X) (bY : Completion l E Y),
          Nonempty (CompletedPull l E g a bX bY)) ∧
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (U : Y.ProEt)
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l Y E),
      integralCoefficientRestrictionNormalized l E f c → Nonempty (Ambient f U _ _ c)) ∧
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (U : Y.ProEt)
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l Y E),
      rationalCoefficientRestrictionNormalized l E f c → Nonempty (Ambient f U _ _ c)) := sorry

end AlgebraicGeometry.Scheme.ContinuousSlice
