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
import all Sheaf.Paper.CompletedTowerDirectImage
import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso
import Sheaf.Paper.RealizationCoefficientSquare
import Sheaf.Paper.RealizationContinuousDirectImage
import Sheaf.Paper.RealizationCompletedImage
import Sheaf.Paper.RealizationScalarPushMate
import Sheaf.Paper.SfIntegralDirectImageConstructible
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

set_option linter.unusedSectionVars false in
private theorem integralCoefficient_isIso :
    IsIso (completedCoefficientMap h (pbcIntegralDatum l E)) :=
  completedCoefficient_isIso h (pbcIntegralDatum l E)

set_option linter.unusedSectionVars false in
private theorem globalUnit (W : Scheme.{u})
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))] : IsUnit (l : Γ(W, ⊤)) := by
  apply W.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ
  intro x _
  simpa only [map_natCast] using (Fact.out : ∀ t : W, IsUnit (l : W.presheaf.stalk t)) x

private theorem detailedEncoding_eq (W : Scheme.{u}) :
    (realizationDetailedEncoding l E W).functor = integralDetailedTransport W l E := by
  rfl

private theorem scalarPushComparison_exists
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LT : A ⥤ B} {RT : B ⥤ A} {LU : C ⥤ D} {RU : D ⥤ C}
    (adjT : LT ⊣ RT) (adjU : LU ⊣ RU) (G : A ⥤ C) (H : B ⥤ D)
    (d : H ⋙ RU ≅ RT ⋙ G) :
    ∃ β : G ⋙ LU ⟶ LT ⋙ H, ∀ K : A,
      adjU.homEquiv _ _ (β.app K) =
        G.map (adjT.unit.app K) ≫ d.inv.app (LT.obj K) := by
  refine ⟨Adjunction.pushHomOfComapIso adjT adjU d, fun K ↦ ?_⟩
  exact (unit_mateEquiv_symm adjT adjU (TwoSquare.mk _ _ _ _ d.inv) K).symm

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
  classical
  let := integralCoefficient_isIso l E h
  let cA := asIso (completedCoefficientMap h (pbcIntegralDatum l E))
  have hcA : cA.hom = completedCoefficientMap h (pbcIntegralDatum l E) := rfl
  let cE := asIso (rationalContinuousPullback l E h)
  have hcE : rationalCoefficientRestrictionNormalized l E h cE.hom :=
    rationalContinuousPullback_normalized l E h
  have sq : cA.hom ≫ sT.scalarMap l E T =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (sU.scalarMap l E U) ≫
        cE.hom := realizationCoefficientSquare l E h sT sU
  let G := proEtaleRingDerivedDirectImage h _ _ cA
  let H := proEtaleRingDerivedDirectImage h _ _ cE
  let d := proEtaleRingRestrictionDerivedDirectImage h
    (pbcAdicCompletion U (pbcIntegralDatum l E)) (rationalCoefficientSheaf l U E)
    (pbcAdicCompletion T (pbcIntegralDatum l E)) (rationalCoefficientSheaf l T E)
    (sU.scalarMap l E U) (sT.scalarMap l E T) cA cE sq
  obtain ⟨β, hβ⟩ := scalarPushComparison_exists
    (pbcDerivedScalarAdjunction (sT.scalarMap l E T))
    (pbcDerivedScalarAdjunction (sU.scalarMap l E U)) G H d
  obtain ⟨econt⟩ := realizationContinuousDirectImage l E h sT sU cE hcE
  let i := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
  have closed (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))] :
      ObjectProperty.IsClosedUnderIsomorphisms
        (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) :=
    (pbcIntegralUniformComplete_isTriangulated l E W Fact.out Fact.out).1
  let := closed T
  let := closed U
  have detailed (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
      (M : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
      sfIntegralConstructible l E W ((realizationDetailedEncoding l E W).inverse.obj M.obj) := by
    apply (integralStratifiedPerfectDetailed W l E Fact.out (globalUnit l W) _).mpr
    rw [← detailedEncoding_eq]
    exact ObjectProperty.prop_of_iso _
      ((realizationDetailedEncoding l E W).counitIso.app M.obj).symm M.property
  have hl : IsUnit (l : k) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd : ringChar k ∣ l := (CharP.cast_eq_zero_iff k (ringChar k) l).mp hz
    have he : ringChar k = l := ((Fact.out : l.Prime).eq_one_or_self_of_dvd
      (ringChar k) hd).resolve_left (Fact.out : (ringChar k).Prime).ne_one
    exact (Fact.out : ringChar k ≠ l) he
  have image (M : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) :
      ∃ hp : HasProduct (sfDirectImageTerm l E h
          ((realizationDetailedEncoding l E T).inverse.obj M.obj)),
        ∃ L : @SfIntegralDirectImage l _ E _ _ _ T U h
            ((realizationDetailedEncoding l E T).inverse.obj M.obj) hp,
          sfIntegralConstructible l E U L.obj ∧
          Nonempty (G.obj M.obj ≅ (realizationDetailedEncoding l E U).functor.obj L.obj) := by
    let K := (realizationDetailedEncoding l E T).inverse.obj M.obj
    have hK := detailed T M
    obtain ⟨⟨hp, ⟨L⟩⟩, hL, _⟩ := sfIntegralDirectImage_constructible k l hl E h K hK
    let := hp
    obtain ⟨e⟩ := realizationCompletedImage l E h cA hcA K hK.1 L
    refine ⟨hp, L, (hL L).1, ⟨?_⟩⟩
    exact G.mapIso ((realizationDetailedEncoding l E T).counitIso.app M.obj).symm ≪≫ e
  refine ⟨{
    integralPullback := cA
    integralPullback_normalization := hcA
    rationalPullback := cE
    rationalPullback_normalization := hcE
    coefficient_square := sq
    continuous_direct_image := econt
    integral := ?_
    completed := ?_
    beta := Functor.whiskerLeft i β
    beta_isIso := ?_
    beta_normalization := fun M ↦ hβ M.obj }⟩
  · intro M
    obtain ⟨hp, L, hL, ⟨e⟩⟩ := image M
    apply ObjectProperty.prop_of_iso _ e.symm
    rw [detailedEncoding_eq]
    exact (integralStratifiedPerfectDetailed U l E Fact.out (globalUnit l U) _).mp hL
  · intro M
    obtain ⟨hp, L, _, e⟩ := image M
    exact ⟨hp, L, e⟩
  · intro M
    have : QuasiCompact h := inferInstance
    have : QuasiSeparated h := inferInstance
    have hb := (integralStratifiedPerfectCharacterization T l E Fact.out
      (globalUnit l T) M.obj)
    obtain ⟨a, b, _, ha, _⟩ := (hb.2.mp (hb.1.mp M.property)).1
    exact realizationScalarPushMate_isIso l E h sT sU cA hcA cE hcE sq
      M.obj ⟨a, ha⟩ (β.app M.obj) (hβ M.obj)

end WeilConjectures
