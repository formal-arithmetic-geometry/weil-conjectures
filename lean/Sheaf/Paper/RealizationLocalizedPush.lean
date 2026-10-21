/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.CompletedTowerDirectImage
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.ContinuousIntegralLocalization
import Sheaf.Paper.ContinuousIntegralLocalizationHomology
import Sheaf.Paper.ContinuousIntegralLocalizationContinuity
import Sheaf.Paper.ContinuousChartSchemeNaturality
import Sheaf.Paper.ContinuousCoefficientRealizations
import Sheaf.Paper.ContinuousModuleEncodingScalarExtension
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The normalized localization comparison for ordinary derived direct image

Source: Bhatt--Scholze, Lemma 6.7.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-localized-push)

All direct images below are ordinary ambient direct images. The rational one is
written in sectionwise module coordinates under the published internal-module encoding.
The coefficient identifications and the adjunction equation specify the comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- The existing coefficient-isomorphism encoding of the detailed completed category.
Source: Bhatt--Scholze, Definition 6.5.1, and the quotient-normalized comparison
in integralStratifiedPerfectDetailed.
(blueprint: lem-weil-pbc-realization-localized-push) -/
abbrev realizationDetailedEncoding (T : Scheme.{u}) :=
  let e := ringModuleEquivalenceOfIso T (integralDetailedCoefficientComparison T l E)
  letI := Functor.additive_of_preserves_binary_products e.functor
  letI := Functor.additive_of_preserves_binary_products e.inverse
  e.mapDerivedCategory

/-- The normalized scalar-extension coefficient map supplied by the scalar-functor node.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-localized-push) -/
abbrev RealizationScalarFunctorData.scalarMap (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) := s.integralIso.hom ≫ s.inclusion

/-- The published internal-module encoding, derived termwise with its specified
additive structures. Source: Bhatt--Scholze, Section 6.8 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-localized-push) -/
abbrev RealizationScalarFunctorData.moduleEncoding (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E T) :=
  let e := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso s.sectionIso).symm)
  letI := s.encodingAdditive
  letI := s.encodingInverseAdditive
  e.mapDerivedCategory

variable {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
variable (h : T ⟶ U)
  (sT : RealizationScalarFunctorData l E T) (sU : RealizationScalarFunctorData l E U)

/-- The canonical coefficient comparisons, integral stability, completed-image agreement,
and normalized scalar/direct-image comparison. The equation for beta is its adjunction
normalization, using the published coefficient-restriction comparison d.
Source: Bhatt--Scholze, Lemma 6.7.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-localized-push) -/
structure RealizationLocalizedPushData where
  integralPullback : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (pbcAdicCompletion U (pbcIntegralDatum l E)) ≅
    pbcAdicCompletion T (pbcIntegralDatum l E)
  integralPullback_normalization : integralPullback.hom =
    completedCoefficientMap h (pbcIntegralDatum l E)
  rationalPullback : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l U E) ≅ rationalCoefficientSheaf l T E
  rationalPullback_normalization :
    rationalCoefficientRestrictionNormalized l E h rationalPullback.hom
  coefficient_square : integralPullback.hom ≫ sT.scalarMap l E T =
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (sU.scalarMap l E U) ≫
      rationalPullback.hom
  continuous_direct_image :
    (sT.moduleEncoding l E T).inverse ⋙
        (lowerStar (Profinite.continuousCoefficientRingObj E) h).rightDerivedFunctor ⋙
          (sU.moduleEncoding l E U).functor ≅
      proEtaleRingDerivedDirectImage h _ _ rationalPullback
  integral : ∀ M : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete U (pbcIntegralDatum l E)
      ((proEtaleRingDerivedDirectImage h _ _ integralPullback).obj M.obj)
  completed : ∀ M : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
    ∃ hprod : HasProduct (sfDirectImageTerm l E h
        ((realizationDetailedEncoding l E T).inverse.obj M.obj)),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ T U h
          ((realizationDetailedEncoding l E T).inverse.obj M.obj) hprod,
        Nonempty ((proEtaleRingDerivedDirectImage h _ _ integralPullback).obj M.obj ≅
          (realizationDetailedEncoding l E U).functor.obj L.obj)
  beta : ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
      proEtaleRingDerivedDirectImage h _ _ integralPullback ⋙
        pbcDerivedExtend (sU.scalarMap l E U) ⟶
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
      pbcDerivedExtend (sT.scalarMap l E T) ⋙
        proEtaleRingDerivedDirectImage h _ _ rationalPullback
  beta_isIso : ∀ M : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
    IsIso (beta.app M)
  beta_normalization : ∀ M : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E),
    (pbcDerivedScalarAdjunction (sU.scalarMap l E U)).homEquiv _ _ (beta.app M) =
      (proEtaleRingDerivedDirectImage h _ _ integralPullback).map
          ((pbcDerivedScalarAdjunction (sT.scalarMap l E T)).unit.app M.obj) ≫
        (proEtaleRingRestrictionDerivedDirectImage h
          (pbcAdicCompletion U (pbcIntegralDatum l E)) (rationalCoefficientSheaf l U E)
          (pbcAdicCompletion T (pbcIntegralDatum l E)) (rationalCoefficientSheaf l T E)
          (sU.scalarMap l E U) (sT.scalarMap l E T)
          integralPullback rationalPullback coefficient_square).inv.app
            ((pbcDerivedExtend (sT.scalarMap l E T)).obj M.obj)

/-- Ordinary ambient integral direct image is integral constructible, agrees with the
specified completed image, and commutes with scalar localization by the canonical beta.
Naturality is the natural-transformation field, and no properness assumption is made.
Source: Bhatt--Scholze, Lemma 6.7.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-localized-push)

Proof:
1. Use continuous coefficient realization, chart scheme naturality, and profinite-point
pullback composition to identify coefficient maps with precomposition. Module encodings
commute with restriction, so the canonical comparison of scalar left adjoints respects
units. Exact encodings descend termwise and intertwine direct image.
2. Finite-type separated schemes over a field, and their morphism h, are qcqs. The
valuation ring is a DVR with finite residue field, and l is a unit times a positive
uniformizer power. Positive quotients are finite perfect modules. Integral stratified
perfect characterization supplies boundedness and the detailed integral convention.
3. Direct-image/derived-limit comparison identifies ordinary Rh_* with the completed
quotient tower. Ringed-topos derived composition identifies its terms and transitions
with the specified finite direct images. Integral direct-image constructibility gives
membership on U, and integralStratifiedPerfectDetailed transports the convention.
4. Define beta as the scalar-adjunction adjunct of Rh_*(eta_T), followed by d inverse.
The unit-adjunct identity is exactly beta_normalization. Naturality of units and d
makes beta natural in M.
5. Integral localization homology and qcqs push continuity identify the two restricted
vertices on cohomology with the same l-multiplication telescope on H^q(Rh_*M).
6. The normalization intertwines all legs l^(-n) eta: additive maps commute with l
and its inverse on localized vertices. The colimit universal property therefore makes
the restricted beta an isomorphism on every cohomology sheaf.
7. Represent the map into a K-injective resolution. Its cohomology isomorphisms make
the representing chain map a quasi-isomorphism, invertible in the derived category.
Coefficient restriction reflects isomorphisms, so beta is invertible. All continuity
arguments used qcqs, not properness. -/
theorem realization_localized_push (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [h.IsOver (Spec (.of k))] :
    Nonempty (RealizationLocalizedPushData l E h sT sU) := by
  sorry

end WeilConjectures
