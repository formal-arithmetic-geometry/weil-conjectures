/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.Paper.BoundaryExceptionalComparisonData
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport

/-! # Restricting site comparison to finite Tor amplitude

Source: boundary finite-site realization, proof step 1
(blueprint: lem-weil-boundary-finite-tor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.BoundaryFiniteSite
open BoundaryComparison

private theorem finiteSupport_iff {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C) :
    Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C q).obj K)} ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor C q).obj K) := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun q hq ↦ ?_⟩
    by_contra hn
    rcases hq with hq | hq
    · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hq
    · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hq
  · rintro ⟨a, b, _, h⟩
    apply (Set.finite_Icc a b).subset
    intro q hq
    exact ⟨le_of_not_gt (fun hqa ↦ hq (h q (Or.inl hqa))),
      le_of_not_gt (fun hbq ↦ hq (h q (Or.inr hbq)))⟩

private theorem intrinsicBounded_iff_origin
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    Scheme.intrinsicFiniteTorsionConstructible l E n hn T K ↔
      ∃ H : Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T,
        Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T H ∧
        Nonempty ((finiteCoefficientIntrinsicDerivedComparison T
          (Padic.coefficientExtensionRing l E n)).obj H ≅ K) := by
  have := Padic.finite_coefficientExtensionRing l E n hn
  have h := (Scheme.finiteRing_constructibleDerived_origin T
    (Padic.coefficientExtensionRing l E n)).2.2.1 K
  rw [Scheme.intrinsicFiniteTorsionConstructible, finiteSupport_iff]
  rw [and_comm, ← h]
  constructor
  · rintro ⟨H, ⟨e⟩⟩
    exact ⟨H.obj, H.property, ⟨e⟩⟩
  · rintro ⟨H, hH, ⟨e⟩⟩
    exact ⟨⟨H, hH⟩, ⟨e⟩⟩

/-- Comparison restricts to the published finite-Tor constructible subcategories.
Source: boundary finite-site realization, step 1; constructible origin and comparison
of Tor intervals (blueprint: lem-weil-boundary-finite-tor-comparison).

Proof: finiteRing_constructibleDerived_origin identifies bounded constructible complexes
in the intrinsic presentation of pro-etale coefficient sheaves. The canonical intrinsic
coefficient realization is an exact equivalence, so its cohomology comparison transports
this equivalence to fixed scalar modules. On a bounded etale object, form its D+ lift.
torAmplitudeIn_mapDerivedCategory_iff and intrinsic Tor-amplitude transport
identify each ordered Tor interval. Thus the comparison equivalence preserves and
reflects existence of a finite interval. Restrict it to these full subcategories.
For a pro-etale finite-Tor object, take its bounded constructible etale representative;
reflection of its Tor interval makes this representative finite Tor. The restricted
functor is the actual comparison by the natural isomorphism of the constructible-origin
equivalence. This also supplies the last assertion, with no chosen object definition. -/
theorem boundary_finite_tor_comparison
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) :
    letI : Finite (Padic.coefficientExtensionRing l E n) :=
      Padic.finite_coefficientExtensionRing l E n hn
    let C := coefficients (Padic.coefficientExtensionRing l E n)
    let Pe := WeilConjectures.finiteTorConstructibleEtale l E n hn T
    let Pp := WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn T
    let F := comparison C T
    (∃ e : Pe.FullSubcategory ≌ Pp.FullSubcategory,
      Nonempty (e.functor ⋙ Pp.ι ≅ Pe.ι ⋙ F)) ∧
    (∀ (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C)), Pe K.obj →
      ∀ (a b : ℤ), a ≤ b →
        (Etale.DerivedCategory.hasTorAmplitudeIn
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) T a b K.obj ↔
          ProEtale.DerivedCategory.torAmplitudeIn C T a b (F.obj K.obj))) ∧
    (∀ K, Pp K → ∃ H, Pe H ∧ Nonempty (F.obj H ≅ K)) := by
  classical
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := Padic.coefficientExtensionRing l E n
  let Λ := ULift.{u + 1, u} A
  let C := coefficients A
  let Pe := WeilConjectures.finiteTorConstructibleEtale l E n hn T
  let Pp := WeilConjectures.finiteTorConstructibleProEtaleModule l E n hn T
  let ν := comparisonUpperStar C T
  let F := comparison C T
  let R := finiteCoefficientIntrinsicRealization T A
  have : R.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact T A).1
  have hplus (H : Pe.FullSubcategory) : DerivedCategory.TStructure.t.plus H.obj := by
    obtain ⟨a, b, _, hz⟩ := H.property.1.2
    exact ⟨a, (DerivedCategory.isGE_iff H.obj a).2 (fun q hq ↦ hz q (Or.inl hq))⟩
  have hinterval (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology C))
      (a b : ℤ) :
      Etale.DerivedCategory.hasTorAmplitudeIn Λ T a b K.obj ↔
        ProEtale.DerivedCategory.torAmplitudeIn C T a b (F.obj K.obj) :=
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := Λ) (K := K.obj)).trans
      (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
        (Λ := Λ) a b K.obj).symm
  have himage (H : Pe.FullSubcategory) : Pp (F.obj H.obj) := by
    refine ⟨(intrinsicBounded_iff_origin l E n hn T _).2 ?_, ?_⟩
    · exact ⟨H.obj, H.property.1, ⟨(Functor.mapDerivedCategoryCompIso ν R).app H.obj⟩⟩
    · obtain ⟨a, b, hab, ht⟩ := H.property.2
      exact ⟨a, b, (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
        A T a b hab _).2 ((hinterval ⟨H.obj, hplus H⟩ a b).1 ht)⟩
  have horigin (K) (hK : Pp K) : ∃ H, Pe H ∧ Nonempty (F.obj H ≅ K) := by
    obtain ⟨H, hH, ⟨e⟩⟩ := (intrinsicBounded_iff_origin l E n hn T _).1 hK.1
    let e' : F.obj H ≅ K := R.mapDerivedCategory.preimageIso
      (((Functor.mapDerivedCategoryCompIso ν R).app H).symm ≪≫ e)
    have hHplus : DerivedCategory.TStructure.t.plus H := by
      obtain ⟨a, b, _, hz⟩ := hH.2
      exact ⟨a, (DerivedCategory.isGE_iff H a).2 (fun q hq ↦ hz q (Or.inl hq))⟩
    obtain ⟨a, b, ht⟩ := hK.2
    have ht' := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A T a b ht.1 K).1 ht
    have hf : ProEtale.DerivedCategory.torAmplitudeIn C T a b (F.obj H) :=
      (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e'.symm ht'
    exact ⟨H, ⟨hH, a, b, ht.1, (hinterval ⟨H, hHplus⟩ a b).2 hf⟩, ⟨e'⟩⟩
  let J := Pp.lift (Pe.ι ⋙ F) himage
  have hbij (H K : Pe.FullSubcategory) : Function.Bijective
      (fun f : H.obj ⟶ K.obj ↦ F.map f) :=
    bijective_comparisonUpperStar_mapDerivedCategory_map H.obj K.obj (hplus K)
  have : J.Full := ⟨fun {H K} f ↦ by
    obtain ⟨g, hg⟩ := (hbij H K).2 f.hom
    exact ⟨Pe.homMk g, Pp.hom_ext hg⟩⟩
  have : J.Faithful := ⟨fun {H K} f g h ↦
    Pe.hom_ext ((hbij H K).1 (congrArg (·.hom) h))⟩
  have : J.EssSurj := ⟨fun K ↦ by
    obtain ⟨H, hH, ⟨e⟩⟩ := horigin K.obj K.property
    exact ⟨⟨H, hH⟩, ⟨Pp.isoMk e⟩⟩⟩
  have : J.IsEquivalence := {}
  exact ⟨⟨J.asEquivalence, ⟨Iso.refl _⟩⟩, fun K _ a b _ ↦ hinterval K a b, horigin⟩

end AlgebraicGeometry.ProEtale.BoundaryFiniteSite
