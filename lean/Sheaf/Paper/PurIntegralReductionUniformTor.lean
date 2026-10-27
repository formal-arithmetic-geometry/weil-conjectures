/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72, SHEAF group T9
-/
module

public import Sheaf.Paper.PurIntegralFinitePerfectCharts
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.CategoryTheory.DerivedMorphismPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Sheaf.Paper.StratifiedFiniteProjectiveTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Uniform Tor bounds for finite lists of integral reductions

Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.6.10(1)
(blueprint: lem-pur-integral-reduction-uniform-tor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

private theorem pur_quotient_terms {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : ∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q))
    (n : ℕ) (q : ℤ) :
    Module.Projective (PbcQuotient d n) ((purScalarReductionComplex d P n).X q) ∧
      Module.Finite (PbcQuotient d n) ((purScalarReductionComplex d P n).X q) := by
  let φ := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let : Algebra A (PbcQuotient d n) := φ.toAlgebra
  have := (hP q).1
  have := (hP q).2
  change Module.Projective (PbcQuotient d n) (TensorProduct A (PbcQuotient d n) (P.X q)) ∧
    Module.Finite (PbcQuotient d n) (TensorProduct A (PbcQuotient d n) (P.X q))
  constructor <;> infer_instance

private theorem pur_chart_homology
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B] (U : X.ProEt)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)))
    (P : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hP : ∀ q : ℤ, Module.Finite B (P.X q))
    (e : Nonempty (purFixedChart X B U K ≅
      DerivedCategory.Q.obj (((constantSheaf ((ProEt.topology X).over U)
        (ModuleCat.{u + 1} B)).mapHomologicalComplex (.up ℤ)).obj P)))
    (q : ℤ) :
    ∃ M : ModuleCat.{u + 1} B, Finite M ∧ Nonempty
      ((((DerivedCategory.homologyFunctor _ q).obj K).over U) ≅
        (constantSheaf ((ProEt.topology X).over U) (ModuleCat.{u + 1} B)).obj M) := by
  let G := (ProEt.topology X).overPullback (ModuleCat.{u + 1} B) U
  let F := constantSheaf ((ProEt.topology X).over U) (ModuleCat.{u + 1} B)
  have := hP q
  have : Finite (P.X q) := Module.finite_of_finite (R := B)
  have : Finite (P.cycles q) := Finite.of_injective (P.iCycles q)
    ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have hM : Finite (P.homology q) := Finite.of_surjective (P.homologyπ q)
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  refine ⟨P.homology q, hM, ⟨?_⟩⟩
  exact (G.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e.some ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫ (P.sc q).mapHomologyIso F

private theorem pur_finite_cover_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (m : ℕ) (U : Fin m → X.ProEt)
    (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 X))
    (hcover : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (he : ∀ c : Fin m, ∃ M : ModuleCat.{u + 1} B, Finite M ∧
      Nonempty (F.over (U c) ≅
        (constantSheaf ((ProEt.topology X).over (U c)) (ModuleCat.{u + 1} B)).obj M)) :
    ProEtale.IsFiniteLocallyConstant B F := by
  classical
  let I := ULift.{u + 1} (Fin m)
  have hcover' : Presieve.ofArrows (fun c : I ↦ (U c.down).left)
      (fun c ↦ (U c.down).hom) ∈ proetalePrecoverage X := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hcover
    have hw (c : Fin m) : (f c).left = (U c).hom := by
      have h := MorphismProperty.Over.w (f c)
      change (f c).left ≫ 𝟙 X = (U c).hom at h
      change (f c).left ≫ 𝟙 X = (U c).hom
      exact (Category.comp_id _).symm.trans h
    have hr : Presieve.ofArrows (fun c : I ↦ (U c.down).left)
        (fun c ↦ (U c.down).hom) =
        Presieve.ofArrows (fun c : Fin m ↦ (U c).left) (fun c ↦ (f c).left) := by
      simp only [hw]
      funext V g
      apply propext
      constructor
      · rintro ⟨c⟩
        exact Presieve.ofArrows.mk c.down
      · rintro ⟨c⟩
        exact Presieve.ofArrows.mk (ULift.up c)
    rw [hr]
    exact hcover
  refine ⟨I, fun c ↦ (U c.down).left, fun c ↦ (U c.down).hom, hcover', ?_⟩
  intro c
  obtain ⟨M, hM, ⟨e⟩⟩ := he c.down
  let V := U c.down
  have := ProEt.sliceDense X V
  let E := (ProEt.sliceEquiv X V).sheafCongr
    ((ProEt.topology X).over V) (ProEt.topology V.left) (ModuleCat.{u + 1} B)
  let r : E.functor.obj (F.over V) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) V.hom V.prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let ec := ((ProEt.sliceEquiv X V).constantSheafSheafCongrIso
    ((ProEt.topology X).over V) (ProEt.topology V.left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := V))).app M
  exact ⟨M, hM, ⟨(ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) V.hom V.prop).app F ≪≫ r.symm ≪≫
      E.functor.mapIso e ≪≫ ec⟩⟩

private theorem pur_constructible_of_charts
    (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} B)))
    (S : Stratification T) (hS : 0 < S.n)
    (hmodels : ∀ r : Fin S.n,
      ∃ (m : ℕ) (U : Fin m → (S.domain r).ProEt)
        (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 (S.domain r))),
        Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain r)).coverings _ ∧
        ∀ (c : Fin m) (q : ℤ),
          ∃ M : ModuleCat.{u + 1} B, Finite M ∧ Nonempty
            ((((DerivedCategory.homologyFunctor _ q).obj
              (((ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion r))
                |>.mapDerivedCategory).obj K)).over (U c)) ≅
              (constantSheaf ((ProEt.topology (S.domain r)).over (U c))
                (ModuleCat.{u + 1} B)).obj M)) :
    ∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf T B
      ((DerivedCategory.homologyFunctor _ q).obj K) := by
  intro q
  refine ⟨S, hS, S.isConstructible_stratum, fun r ↦ ?_⟩
  obtain ⟨m, U, f, hf, he⟩ := hmodels r
  let G := ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion r)
  let H := (DerivedCategory.homologyFunctor _ q).obj (G.mapDerivedCategory.obj K)
  have hh : ProEtale.IsFiniteLocallyConstant B H :=
    pur_finite_cover_models (S.domain r) B H m U f hf (fun c ↦ he c q)
  have h := ProEtale.isFiniteLocallyConstant_of_iso
    ((G.mapDerivedCategoryHomologyFunctorIso q).symm.app K) hh
  obtain ⟨I, V, g, hg, hm⟩ := ProEtale.finiteModels_over B _ h
  exact ⟨⟨I, V, g, hg, fun c ↦ ⟨(hm c).choose, (hm c).choose_spec.2⟩⟩,
    ProEtale.finite_geometricStalk_of_finite_models B _ h⟩

private theorem pur_origin_bounded
    (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (L : Etale.DerivedCategoryModule B T)
    (R : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} B)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.obj L ≅ R)
    (hc : ∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf T B
      ((DerivedCategory.homologyFunctor _ q).obj R))
    (a b : ℤ) (hab : a ≤ b)
    (ht : ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) T a b R) :
    Etale.DerivedCategory.isBoundedConstructible B T L := by
  let F := comparisonUpperStar (ModuleCat.{u + 1} B) T
  let hE (q : ℤ) := (F.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e
  have hconst (q : ℤ) : ProEtale.IsConstructible B
      (F.obj ((DerivedCategory.homologyFunctor _ q).obj L)) := by
    obtain ⟨S, _, _, hS⟩ := hc q
    apply ProEtale.isConstructible_of_iso (hE q).symm
    exact ⟨S, fun i ↦ finite_models_of_fixed_lisse (S.domain i) B _ (hS i)⟩
  refine ⟨?_, a, b, hab, ?_⟩
  · intro q
    obtain ⟨G, hG, ⟨eG⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B (hconst q)
    have : IsConstructibleSheaf G := hG
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.of_iso (F.preimageIso eG))
  · intro q hq
    apply F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    have hb := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj R) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff R a).mp hb.1 q hq
      · exact (DerivedCategory.isLE_iff R b).mp hb.2 q hq
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e)

/-- A finite family in the completed integral constructible category has one finite
constructible stratification and one Tor interval for every positive reduction.
The finite local perfect complexes and their termwise quotient complexes are retained.
The same bounds hold on every stratum, and the retained compatible etale origins are
bounded constructible. If the whole family is zero the chosen interval is [0,0].

Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.6.10(1), Definition 6.5.1;
Stacks Tag 06YS (blueprint: lem-pur-integral-reduction-uniform-tor).

Proof: choose the simultaneous finite perfect charts and common term interval from
pur_integral_finite_perfect_charts. Scalar extension preserves finite projective
terms and their strict bounds. Exact slice restriction commutes with homology,
so each reduced chart has the finite constant value given by scalar homology.
Transport these models through the slice equivalence to obtain finite locally
constant stratum restrictions, and hence intrinsic constructibility.
Apply stratified_finite_projective_tor to the same quotient complexes: bounded
flat scalar terms control every degree-zero sheaf tensor test on the charts,
and conservative cover and stratum pullbacks detect global vanishing.
Retain the compatible witnessed towers already supplied by membership. Their
origins pull back to the reductions under the canonical coefficient equivalence.
Constructible homology descends through comparison, and exact conservative
comparison detects the cohomological bounds obtained from the Tor interval.
Thus those same origins are bounded constructible, with their normalization
equations unchanged. Finally compare the finite-value and finite-stalk notions
of etale constructibility to obtain the source constructibleFiniteTor predicate.
The chart lemma supplies the stipulated all-zero and empty-family choices. -/
theorem pur_integral_reduction_uniform_tor
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (s : ℕ) (K : Fin s → PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (_hK : ∀ j : Fin s,
      IsPbcBoundedConstructibleComplete T l E (K j)) :
    ∃ a b : ℤ, a ≤ b ∧
      ((∀ j : Fin s, IsZero (K j)) → a = 0 ∧ b = 0) ∧
      ∃ S : Stratification T, 0 < S.n ∧
        (∀ (j : Fin s) (n : ℕ),
          (∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf T
            (PbcQuotient (pbcPadicCoefficientDatum l E) n)
            ((DerivedCategory.homologyFunctor _ q).obj
              (purIntegralReduction T (pbcPadicCoefficientDatum l E) (K j) n))) ∧
          AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn
            (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n)) T a b
            (purIntegralReduction T (pbcPadicCoefficientDatum l E) (K j) n) ∧
          AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n)) T
            (purIntegralReduction T (pbcPadicCoefficientDatum l E) (K j) n) ∧
          ∀ r : Fin S.n, AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn
            (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n))
            (S.domain r) a b
            (purReductionOnStratum (S.immersion r) (pbcPadicCoefficientDatum l E) (K j) n)) ∧
        (∀ (r : Fin S.n) (j : Fin s),
          ∃ (m : ℕ) (U : Fin m → (S.domain r).ProEt)
            (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 (S.domain r)))
            (P : Fin m → CochainComplex
              (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ),
            Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain r)).coverings _ ∧
            ∀ c : Fin m,
              ((P c).IsStrictlyGE a ∧ (P c).IsStrictlyLE b) ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E)
                ((P c).X q) ∧ Module.Finite (Padic.coefficientExtensionIntegers l E)
                  ((P c).X q)) ∧
              Nonempty (integralLocalDerived (S.immersion r)
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)) (U c) (K j) ≅
                integralLocalDerived (S.immersion r)
                  (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)) (U c)
                  ((integralConstantDerived T (pbcPadicCoefficientDatum l E)).obj
                    ((completedConstantQ _).obj (P c)))) ∧
              ∀ n : ℕ,
                (∀ q : ℤ,
                  Module.Projective (PbcQuotient (pbcPadicCoefficientDatum l E) n)
                    ((purScalarReductionComplex (pbcPadicCoefficientDatum l E) (P c) n).X q) ∧
                  Module.Finite (PbcQuotient (pbcPadicCoefficientDatum l E) n)
                    ((purScalarReductionComplex (pbcPadicCoefficientDatum l E) (P c) n).X q)) ∧
                Nonempty (purFixedChart (S.domain r)
                  (PbcQuotient (pbcPadicCoefficientDatum l E) n) (U c)
                  (purReductionOnStratum (S.immersion r)
                    (pbcPadicCoefficientDatum l E) (K j) n) ≅
                  purScalarComplexOnChart (S.domain r) (pbcPadicCoefficientDatum l E)
                    (U c) (P c) n) ∧
                ∀ q : ℤ,
                  ∃ M : ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n),
                    Finite M ∧ Nonempty
                      ((((DerivedCategory.homologyFunctor _ q).obj
                        (purReductionOnStratum (S.immersion r)
                          (pbcPadicCoefficientDatum l E) (K j) n)).over (U c)) ≅
                        ((constantSheaf ((ProEt.topology (S.domain r)).over (U c))
                          (ModuleCat.{u + 1} (PbcQuotient
                            (pbcPadicCoefficientDatum l E) n))).obj M))) ∧
        ∀ j : Fin s,
          ∃ (W : PbcWitnessedTower T (pbcPadicCoefficientDatum l E))
            (e : ∀ n : ℕ,
              (pbcDerivedFunctionRealization T (pbcPadicCoefficientDatum l E) n).obj
                (W.K n) ≅
                  (pbcCompletedReduction T (pbcPadicCoefficientDatum l E) n).obj (K j)),
            (∀ n : ℕ, Etale.DerivedCategory.isBoundedConstructible
              (PbcQuotient (pbcPadicCoefficientDatum l E) n) T (W.origin n).L.obj) ∧
            ∀ n : ℕ,
              (pbcDerivedFunctionRealization T (pbcPadicCoefficientDatum l E) n).map
                  (W.theta n).hom ≫ (e n).hom =
                (pbcFunctionReduction T (pbcPadicCoefficientDatum l E) n).inv.app
                    (W.K (n + 1)) ≫
                  (pbcDerivedExtend (pbcAdicQuotient T (pbcPadicCoefficientDatum l E)
                    (n + 1) n (Nat.le_succ n))).map (e (n + 1)).hom ≫
                  (pbcReductionNormalization
                    (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n + 1))
                    (pbcAdicQuotient T (pbcPadicCoefficientDatum l E)
                      (n + 1) n (Nat.le_succ n))
                    (pbcAdicProjection T (pbcPadicCoefficientDatum l E) n)
                    (pbcAdicProjection_comp T (pbcPadicCoefficientDatum l E)
                      (n + 1) n (Nat.le_succ n)) (K j)).hom := by
  classical
  let : IsNoetherian T :=
    isNoetherian_of_locallyOfFiniteType (T ↘ Spec (.of k))
  obtain ⟨a, b, hab, hz, S, hS, hcharts⟩ :=
    pur_integral_finite_perfect_charts l E k p _hpl T s K _hK
  have hc (j : Fin s) (n : ℕ) : ∀ q : ℤ,
      IsConstructibleProEtaleFixedModuleSheaf T
        (PbcQuotient (pbcPadicCoefficientDatum l E) n)
        ((DerivedCategory.homologyFunctor _ q).obj
          (purIntegralReduction T (pbcPadicCoefficientDatum l E) (K j) n)) := by
    apply pur_constructible_of_charts T _ _ S hS
    intro r
    obtain ⟨m, U, f, P, hf, hP⟩ := hcharts r j
    exact ⟨m, U, f, hf, fun c q ↦
      pur_chart_homology _ _ (U c) _ _
        (fun q ↦ (pur_quotient_terms _ _ (hP c).2.1 n q).2)
        ((hP c).2.2.2 n) q⟩
  have ht (j : Fin s) (n : ℕ) :
      ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n)) T a b
        (purIntegralReduction T (pbcPadicCoefficientDatum l E) (K j) n) ∧
      ∀ r : Fin S.n, ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n))
        (S.domain r) a b
        (purReductionOnStratum (S.immersion r) (pbcPadicCoefficientDatum l E) (K j) n) := by
    apply stratified_finite_projective_tor T _ _ a b S
    intro r
    obtain ⟨m, U, f, P, hf, hP⟩ := hcharts r j
    refine ⟨m, U, f, fun c ↦ purScalarReductionComplex
      (pbcPadicCoefficientDatum l E) (P c) n, hf, fun c ↦ ?_⟩
    have : (P c).IsStrictlyGE a := (hP c).1.1
    have : (P c).IsStrictlyLE b := (hP c).1.2
    exact ⟨⟨inferInstance, inferInstance⟩,
      fun q ↦ (pur_quotient_terms _ _ (hP c).2.1 n q).1, (hP c).2.2.2 n⟩
  have ho (j : Fin s) := (_hK j).2.2
  choose W e he using ho
  let eqv (n : ℕ) :=
    (pbcDerivedFunctionRealization T (pbcPadicCoefficientDatum l E) n).asEquivalence
  let eR (j : Fin s) (n : ℕ) :
      (comparisonUpperStar
        (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n)) T).mapDerivedCategory.obj
           ((W j).origin n).L.obj ≅
        purIntegralReduction T (pbcPadicCoefficientDatum l E) (K j) n :=
    (W j).alpha n ≪≫ (eqv n).unitIso.app ((W j).K n) ≪≫
      (eqv n).inverse.mapIso (e j n)
  have hb (j : Fin s) (n : ℕ) :=
    pur_origin_bounded T _ ((W j).origin n).L.obj _ (eR j n) (hc j n) a b hab (ht j n).1
  refine ⟨a, b, hab, hz, S, hS, ?_, ?_, ?_⟩
  · intro j n
    refine ⟨hc j n, (ht j n).1, ?_, (ht j n).2⟩
    refine ⟨?_, a, b, (ht j n).1⟩
    have hbc : Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (PbcQuotient (pbcPadicCoefficientDatum l E) n)) T
        ((W j).origin n).L.obj := by
      obtain ⟨hco, a', b', _, hvan⟩ := hb j n
      refine ⟨⟨⟨a', (DerivedCategory.isGE_iff _ a').2 fun q hq ↦
        hvan q (Or.inl hq)⟩, ⟨b', (DerivedCategory.isLE_iff _ b').2 fun q hq ↦
        hvan q (Or.inr hq)⟩⟩, fun q ↦ ?_⟩
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hco q)
    exact (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).2
      ⟨((W j).origin n).L.obj, hbc, ⟨eR j n⟩⟩
  · intro r j
    obtain ⟨m, U, f, P, hf, hP⟩ := hcharts r j
    refine ⟨m, U, f, P, hf, fun c ↦ ?_⟩
    refine ⟨(hP c).1, (hP c).2.1, (hP c).2.2.1, fun n ↦ ?_⟩
    refine ⟨pur_quotient_terms _ _ (hP c).2.1 n, (hP c).2.2.2 n, ?_⟩
    exact pur_chart_homology _ _ (U c) _ _
      (fun q ↦ (pur_quotient_terms _ _ (hP c).2.1 n q).2) ((hP c).2.2.2 n)
  · intro j
    exact ⟨W j, e j, hb j, he j⟩

end AlgebraicGeometry.Scheme
