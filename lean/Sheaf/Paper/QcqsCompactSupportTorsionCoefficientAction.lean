/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
import Sheaf.Paper.QcqsCompactSupportStrictReductionComparison
import Sheaf.Paper.QcqsCompactSupportFiniteComparison
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Finite coefficient actions on recorded compact-support values

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-torsion-coefficient-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

private theorem projection_transpose
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    {F : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R)
    {S : C ⥤ T} {L : T ⥤ C} (b : S ⊣ L)
    (ev : T ⥤ D) (π : L ⟶ ev ⋙ R) (e : S ⋙ ev ≅ F)
    (hu : ∀ P, b.unit.app P ≫ π.app (S.obj P) =
      a.unit.app P ≫ R.map (e.inv.app P))
    {P Q : C} {N : T} {V : D} (β : S.obj P ⟶ N) (γ : Q ≅ L.obj N)
    (ε : ev.obj N ⟶ V) (d : F.obj Q ⟶ V)
    (hγ : γ.hom ≫ π.app N ≫ R.map ε = a.unit.app Q ≫ R.map d) :
    F.map (b.unit.app P ≫ L.map β ≫ γ.inv) ≫ d =
      e.inv.app P ≫ ev.map β ≫ ε := by
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have hn := a.unit.naturality (b.unit.app P ≫ L.map β ≫ γ.inv)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hn
  calc
    a.unit.app P ≫ R.map (F.map (b.unit.app P ≫ L.map β ≫ γ.inv) ≫ d) =
        (b.unit.app P ≫ L.map β ≫ γ.inv) ≫ a.unit.app Q ≫ R.map d := by
      rw [R.map_comp, ← Category.assoc, ← hn]
      simp only [Category.assoc]
    _ = (b.unit.app P ≫ L.map β ≫ γ.inv) ≫
        γ.hom ≫ π.app N ≫ R.map ε := by rw [hγ]
    _ = b.unit.app P ≫ L.map β ≫ π.app N ≫ R.map ε := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = b.unit.app P ≫ π.app (S.obj P) ≫ R.map (ev.map β) ≫ R.map ε := by
      have hp := π.naturality β
      simp only [Functor.comp_map] at hp
      rw [← Category.assoc (L.map β), hp]
      simp only [Category.assoc]
    _ = a.unit.app P ≫ R.map (e.inv.app P ≫ ev.map β ≫ ε) := by
      rw [← Category.assoc (b.unit.app P), hu]
      simp only [Functor.map_comp, Category.assoc]

private theorem complete_zero_of_reductions
    (W : Scheme.{u}) (A : DerivedCategory (scalarReductionSource l E W))
    (hA : IsSfDerivedComplete l E W A)
    (hzero : ∀ n : ℕ, IsZero ((scalarReductionDerivedExtension l E W n).obj A)) :
    IsZero A := by
  obtain ⟨hp, δ, hδ⟩ := hA
  let := hp
  have hz : IsZero (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj A) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro n
    have := (scalarReductionRestriction_exact l E W n).1
    have := (scalarReductionRestriction_exact l E W n).2
    have : (scalarReductionDerivedRestriction l E W n).Additive := by
      dsimp only [scalarReductionDerivedRestriction]
      infer_instance
    exact ((scalarReductionDerivedRestriction l E W n).map_isZero (hzero n)).eq_of_tgt _ _
  exact Pretriangulated.Triangle.isZero₁_of_isZero₂₃ _ hδ hz hz

private theorem constructible_of_complete_reduction_isos
    (W : Scheme.{u}) {A B : DerivedCategory (scalarReductionSource l E W)}
    (hA : IsSfDerivedComplete l E W A) (hB : sfIntegralConstructible l E W B)
    (e : ∀ n : ℕ, (scalarReductionDerivedExtension l E W n).obj A ≅
      (scalarReductionDerivedExtension l E W n).obj B) :
    sfIntegralConstructible l E W A := by
  obtain ⟨_, a, b, hab, hred⟩ := hB
  refine ⟨hA, a, b, hab, fun n ↦ ?_⟩
  let R := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite R := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) W) :=
    (proEtale_bounded_constructible_isTriangulated W R).1
  refine ⟨ObjectProperty.prop_of_iso _ (e n).symm (hred n).1, ?_⟩
  intro i hi
  apply (hred n).2
  intro hz
  exact hi (((DerivedCategory.homologyFunctor _ i).mapIso (e n)).isZero_iff.mpr hz)

private theorem constructible_isIso_of_reductions
    (W : Scheme.{u}) {A B : DerivedCategory (scalarReductionSource l E W)}
    (a : A ⟶ B) (hA : sfIntegralConstructible l E W A)
    (hB : sfIntegralConstructible l E W B)
    (ha : ∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E W n).map a)) :
    IsIso a := by
  obtain ⟨C, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle a
  obtain ⟨C', hC', ⟨e⟩⟩ := ObjectProperty.ext_of_isTriangulatedClosed₃'
    (sfIntegralConstructible l E W) _ hT hA hB
  have hz : IsZero C' := by
    apply complete_zero_of_reductions l E W C' hC'.1
    intro n
    let R := scalarReductionDerivedExtension l E W n
    obtain ⟨hshift, htri⟩ :=
      (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.1
    let : R.CommShift ℤ := hshift
    have : R.IsTriangulated := htri
    have hzC : IsZero (R.obj C) :=
      Pretriangulated.Triangle.isZero₃_of_isIso₁ _ (R.map_distinguished _ hT) (ha n)
    exact hzC.of_iso (R.mapIso e).symm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp (hz.of_iso e)

private theorem ambient_value_iso
    (K : sfIntegralConstructibleCategory l E X) :
    Nonempty ((image (completed l E) c).obj K.obj ≅
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj) := by
  classical
  obtain ⟨SX, SY, β, γ, hβ, hγ⟩ :=
    qcqsCompactSupport_strictReductionComparison l E K₀ hl c
  let A := (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c
  let τ : A ⟶ sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
      (sfIntegralConstructible l E Y).ι :=
    Functor.whiskerLeft A SY.adjunction.unit ≫
      Functor.whiskerRight (Functor.whiskerLeft (sfIntegralConstructible l E X).ι β)
        (coefficientSequenceLimit l E Y) ≫ γ.inv
  obtain ⟨hcomplete, hfinite⟩ := sfQcqsCompactSupport_finiteComparison l E K₀ hl c K
  have hred (n : ℕ) :
      IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) := by
    have hn := (projection_transpose (coefficientFiniteAdjunction l E Y n) SY.adjunction
      (coefficientSequenceDerivedEvaluation l E Y n) (coefficientSequenceProjection l E Y n)
      (SY.reductionEvaluation n) (fun P ↦ SY.unit_projection P n)
      (β.app K.obj) (γ.app K)
      _ (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom (hγ K n)).trans (hβ K.obj n)
    have := hfinite n
    have : IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom) := by
      change IsIso ((coefficientFiniteDerivedExtension l E Y n).map
        (SY.adjunction.unit.app _ ≫ (coefficientSequenceLimit l E Y).map (β.app K.obj) ≫
          (γ.app K).inv) ≫ _)
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((scalarReductionDerivedExtension l E Y n).map (τ.app K))
      (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom
  have himage := constructible_of_complete_reduction_isos l E Y hcomplete
    ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property
    (fun n ↦ @asIso _ _ _ _
      ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) (hred n))
  have := constructible_isIso_of_reductions l E Y (τ.app K) himage
    ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property hred
  exact ⟨asIso (τ.app K)⟩

/-- A finite quotient action on the input remains a finite quotient action on the
recorded compact-support value. This is an essential-image assertion; no choice of
a finite coefficient presentation is added to the recorded functor.

Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks Tags 0941, 0F7J; the strict quotient
construction in exists_compactSupportRepresentativeComparison.
(blueprint: lem-qcqs-compact-support-torsion-coefficient-action).

Proof: first construct the comparison from the actual compact-support image to
the recorded integral value using the strict reduction-system adjunction and the
recorded gamma. Transposing its projections gives the finite proper/open mates.
Those are isomorphisms by finiteComparison. Completeness and the distinguished
completion triangle show that the cone vanishes, so the comparison itself is an
isomorphism. Only existence is used here, never uniqueness of the normalized lift.
Now present K as the restriction of a finite-coefficient complex M. The actual
proper/open compact-support image commutes with restriction of scalars. Compose
that restriction isomorphism with the image of the presentation and the comparison
to the recorded value. This exhibits the latter as the restriction of the finite
compact-support image of M. Zero input and the empty scheme are included. -/
theorem sfQcqsCompactSupport_torsion_coefficient_action
    (n : ℕ) (K : sfIntegralConstructibleCategory l E X)
    (hK : (scalarReductionDerivedRestriction l E X n).essImage K.obj) :
    (scalarReductionDerivedRestriction l E Y n).essImage
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj := by
  classical
  obtain ⟨M, ⟨e⟩⟩ := hK
  obtain ⟨i⟩ := ambient_value_iso l E K₀ hl c K
  let a := reduction l E (n + 1) (Nat.le_add_left 1 n)
  refine ⟨(image (finite l E (n + 1) (Nat.le_add_left 1 n)) c).obj M, ⟨?_⟩⟩
  exact ((restriction a c).app M).symm ≪≫ (image (completed l E) c).mapIso e ≪≫ i

end WeilConjectures
