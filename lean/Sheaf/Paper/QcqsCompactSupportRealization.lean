/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.QcqsCompactSupportFiniteComparison
import Sheaf.Paper.QcqsCompactSupportNormalizedLift

/-! # Compact-support realization without separated structure morphisms

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tag 0F7J
(blueprint: def-weil-integral-rational-qbar-compact-support).

The object values and the integral and rational actions are the published ones.
The comparison below retains their chosen Roos projections, on every constructible
integral input, without requiring the schemes themselves to be separated over the field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
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

/-- Projection normalization for the ambient realization of the recorded integral functor.
The finite comparison is the actual scalar-adjunction mate of open extension followed
by proper image; its source projection is the chosen Roos projection, not a freely
chosen reduction isomorphism. Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def SfQcqsCompactSupportRealizationSpec
    (τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.hom.app K) ≫
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj K.obj) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
        (finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).obj K.obj) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((finiteReductionIso l E X n).hom.app K.obj)

private theorem complete_zero_of_reductions
    (W : Scheme.{u}) (A : DerivedCategory (scalarReductionSource l E W))
    (hA : IsSfDerivedComplete l E W A)
    (hzero : ∀ n : ℕ, IsZero ((scalarReductionDerivedExtension l E W n).obj A)) :
    IsZero A := by
  obtain ⟨hp, δ, hδ⟩ := hA
  letI := hp
  have hz : IsZero (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj A) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro n
    haveI := (scalarReductionRestriction_exact l E W n).1
    haveI := (scalarReductionRestriction_exact l E W n).2
    haveI : (scalarReductionDerivedRestriction l E W n).Additive := by
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
  letI : Finite R := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  haveI : ObjectProperty.IsClosedUnderIsomorphisms
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
    letI : R.CommShift ℤ := hshift
    haveI : R.IsTriangulated := htri
    have hzC : IsZero (R.obj C) :=
      Pretriangulated.Triangle.isZero₃_of_isIso₁ _ (R.map_distinguished _ hT) (ha n)
    exact hzC.of_iso (R.mapIso e).symm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp (hz.of_iso e)

/-- The projection-normalized realization on the whole integral constructible category.
Source: Bhatt--Scholze, Definition 6.7.6, Lemmas 6.7.7 and 6.1.13
(blueprint: def-weil-integral-rational-qbar-compact-support).

Proof: use the coherent reduction tower of
lem-weil-compact-support-reduction-tower-functor and its actual total right-derived
limit. The integral residue-Tor theorem supplies a common finite Tor interval for all
reductions of each constructible input. Completed open extension commutes with that
normalized tower, using its completion unit. Proper image commutes with total limit
by the right-adjunction comparison. Their composite identifies the actual proper/open
functor, on objects and roofs, with the recorded integral action. The normalized
universal comparisons carry its finite scalar mates to the chosen Roos projections,
which gives the displayed equation and uniqueness. All schemes occurring are finite
type over a field, hence Noetherian and qcqs; none of these arguments uses separatedness
of a structure morphism. The only separated morphism is f, as in the definition. -/
theorem sfQcqsCompactSupportRealization_existsUnique :
    ∃! τ : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportRealizationSpec l E K₀ hl c τ := by
  obtain ⟨τ, hτ, huniq⟩ :=
    sfQcqsCompactSupport_normalizedLift_existsUnique l E K₀ hl c
  have hcomponent (K : sfIntegralConstructibleCategory l E X) : IsIso (τ.app K) := by
    obtain ⟨hcomplete, hfinite⟩ := sfQcqsCompactSupport_finiteComparison l E K₀ hl c K
    have hred (n : ℕ) :
        IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) := by
      haveI := hfinite n
      haveI : IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.app K) ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom) := by
        rw [hτ K n]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K))
        (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom
    have himage := constructible_of_complete_reduction_isos l E Y hcomplete
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property
      (fun n ↦ @asIso _ _ _ _
        ((scalarReductionDerivedExtension l E Y n).map (τ.app K)) (hred n))
    exact constructible_isIso_of_reductions l E Y (τ.app K) himage
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property hred
  letI : ∀ K, IsIso (τ.app K) := hcomponent
  haveI : IsIso τ := NatIso.isIso_of_isIso_app τ
  refine ⟨asIso τ, hτ, ?_⟩
  intro σ hσ
  apply Iso.ext
  exact huniq σ.hom hσ

/-- The canonical realization fixed by the preceding projection normalization.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-weil-integral-rational-qbar-compact-support). -/
def sfQcqsCompactSupportRealization :
    (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι :=
  (sfQcqsCompactSupportRealization_existsUnique l E K₀ hl c).exists.choose

end WeilConjectures
