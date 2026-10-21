/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.FieldWeilShriekShiftData

import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
import Sheaf.Paper.PunctualSpectrumExactFibre

/-! # Mixed upper bounds on the common-stage Weil categories

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-d-dl-general-weights (blueprint: sk-d-dl-general-weights).

Mixed sheaves use the recorded punctual-weight filtration. Cohomology is formed in
fixed pairs using the truncation-normalized Frobenius comparison, without taking a
new derived category of Weil sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The recorded standard t-structure on the geometric fibre. Its geometric
finite-type structures are inherited by base change.
Source: blueprint cohomology clause (blueprint: sk-d-dl-general-weights). -/
def sfWeilStandardTStructure : CategoryTheory.Triangulated.TStructure
    (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left) :=
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Qbar D hl

/-- Underlying degree-b cohomology: truncate to b and shift to degree zero.
Source: blueprint cohomology clause (blueprint: sk-d-dl-general-weights). -/
def sfWeilCohomologyUnderlying (b : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left :=
  constructibleTruncationCohomology (sfWeilStandardTStructure D l hl Qbar Y₀) b

private theorem sfWeilFrobeniusTruncationCompatibility :
    ConstructibleTruncationCompatibility (sfWeilStandardTStructure D l hl Qbar Y₀)
      (sfWeilStandardTStructure D l hl Qbar Y₀)
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar) := by
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  obtain ⟨t, s, units, h⟩ :=
    constructibleTruncations_exists D l hl (D.geometricFiber Y₀).left Qbar
  have hs : s = sfWeilStandardTStructure D l hl Qbar Y₀ :=
    (sfCommonStageStandardTStructure_existsUnique l (D.geometricFiber Y₀).left
      Qbar D hl).unique ⟨h.2.1, h.2.2.2.1⟩
      (sfCommonStageStandardTStructure_existsUnique l (D.geometricFiber Y₀).left
        Qbar D hl).exists.choose_spec
  have hc := h.2.2.2.2.2.2.2 (D.geometricFrobenius Y₀)
  have hu : units = fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x := Subsingleton.elim _ _
  rw [hs, hu] at hc
  exact hc

/-- Upper truncation commutes with the actual fixed-pair Frobenius pullback,
uniquely normalized by its counit. Source: blueprint cohomology clause;
Bhatt--Scholze 6.8.11(3), 6.8.15 (blueprint: sk-d-dl-general-weights).
Proof: apply constructible_pullback_t_exact to geometric Frobenius, whose
underlying scheme morphism is an automorphism. The fibre is finite type by base
change. Transport the recorded comparison to sfWeilPrimeInvertible; invertibility
structures are subsingletons. T-exactness preserves the standard truncation
triangle. The adjunction for upper truncation identifies maps into it by their
composites with its counit, proving the displayed normalization and uniqueness. -/
theorem sfWeilFrobeniusTruncLE_existsUnique (b : ℤ) :
    ∃! e : (sfWeilStandardTStructure D l hl Qbar Y₀).truncLE b ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ⋙
        (sfWeilStandardTStructure D l hl Qbar Y₀).truncLE b,
      ∀ K, e.hom.app K ≫ ((sfWeilStandardTStructure D l hl Qbar Y₀).truncLEι b).app
          ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).obj K) =
        (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map
          (((sfWeilStandardTStructure D l hl Qbar Y₀).truncLEι b).app K) := by
  exact ((sfWeilFrobeniusTruncationCompatibility D l hl Qbar Y₀).1 b).1

/-- The uniquely counit-normalized upper comparison, on the actual pullback.
Source: blueprint cohomology clause (blueprint: sk-d-dl-general-weights). -/
def sfWeilFrobeniusTruncLE (b : ℤ) :=
  (sfWeilFrobeniusTruncLE_existsUnique D l hl Qbar Y₀ b).exists.choose

/-- Lower truncation commutes with actual Frobenius pullback, normalized by its unit.
Source: blueprint cohomology clause; Bhatt--Scholze 6.8.11(3), 6.8.15
(blueprint: sk-d-dl-general-weights).
Proof: apply the same t-exact pullback comparison and subsingleton transport as
for the upper comparison. Lower truncation is left adjoint to the inclusion of
the lower aisle. Its unit determines maps out of the truncation uniquely, giving
the displayed comparison, its naturality, invertibility and uniqueness. -/
theorem sfWeilFrobeniusTruncGE_existsUnique (b : ℤ) :
    ∃! e : (sfWeilStandardTStructure D l hl Qbar Y₀).truncGE b ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ⋙
        (sfWeilStandardTStructure D l hl Qbar Y₀).truncGE b,
      ∀ K, (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map
          (((sfWeilStandardTStructure D l hl Qbar Y₀).truncGEπ b).app K) ≫ e.hom.app K =
        ((sfWeilStandardTStructure D l hl Qbar Y₀).truncGEπ b).app
          ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).obj K) := by
  exact ((sfWeilFrobeniusTruncationCompatibility D l hl Qbar Y₀).1 b).2

/-- The uniquely unit-normalized lower comparison, on the actual pullback.
Source: blueprint cohomology clause (blueprint: sk-d-dl-general-weights). -/
def sfWeilFrobeniusTruncGE (b : ℤ) :=
  (sfWeilFrobeniusTruncGE_existsUnique D l hl Qbar Y₀ b).exists.choose

/-- Frobenius commutes with cohomology by the unique truncation comparisons and
its representative-normalized shift. The truncation comparisons satisfy the canonical
counit and unit equations; the shift is fieldCommonWeilFrobeniusShift, fixed by
signed Roos reindexing at integral representatives. No unspecified shift is chosen.
Source: blueprint cohomology clause; Bhatt--Scholze 6.8.11(3), 6.8.15
(blueprint: sk-d-dl-general-weights). -/
def sfWeilCohomologyFrobenius (b : ℤ) :
    sfWeilCohomologyUnderlying D l hl Qbar Y₀ b ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ⋙
        sfWeilCohomologyUnderlying D l hl Qbar Y₀ b :=
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let t := sfWeilStandardTStructure D l hl Qbar Y₀
  let F := sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar
  let A := t.truncLE b
  let B := t.truncGE b
  let S := shiftFunctor
    (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber Y₀).left) b
  Functor.associator (A ⋙ B) S F ≪≫
    Functor.isoWhiskerLeft (A ⋙ B) (F.commShiftIso b) ≪≫
    (Functor.associator (A ⋙ B) F S).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator A B F ≪≫
        Functor.isoWhiskerLeft A (sfWeilFrobeniusTruncGE D l hl Qbar Y₀ b) ≪≫
        (Functor.associator A F B).symm ≪≫
        Functor.isoWhiskerRight (sfWeilFrobeniusTruncLE D l hl Qbar Y₀ b) B ≪≫
        Functor.associator F A B) S ≪≫
    Functor.associator F (A ⋙ B) S

/-- Cohomology of a fixed pair has underlying object in the constructible heart.
Source: blueprint cohomology clause (blueprint: sk-d-dl-general-weights).
Proof: the truncation tau-ge-b tau-le-b lies in both standard classes in degree b;
shifting by b puts it in both degree-zero classes. The identified standard heart
is sfCommonStageHeartProperty. The induced Frobenius does not change this carrier. -/
theorem sfWeilCohomology_mem (b : ℤ) (K : sfCommonStageWeilComplex D l hl Y₀ Qbar) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar
      (((IsoAlgebra.mapOfNatIso
        (sfWeilCohomologyFrobenius D l hl Qbar Y₀ b)).obj K).carrier) := by
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact
      (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  rw [← (sfCommonStageHeart_properties l (D.geometricFiber Y₀).left Qbar D hl).1]
  let t := sfWeilStandardTStructure D l hl Qbar Y₀
  change t.heart (((t.truncGE b).obj ((t.truncLE b).obj K.carrier))⟦b⟧)
  rw [t.mem_heart_iff]
  constructor
  · exact t.isLE_shift _ b b 0
  · exact t.isGE_shift _ b b 0

/-- The canonical cohomology functor on fixed pairs: its structure is the canonical
Frobenius/cohomology comparison followed by H^b of the given Weil isomorphism.
Only the proof that the explicit carrier lies in the heart is postponed.
Source: blueprint cohomology clause (blueprint: sk-d-dl-general-weights). -/
def sfWeilCohomology (b : ℤ) :
    sfCommonStageWeilComplex D l hl Y₀ Qbar ⥤ sfCommonStageWeilSheaf D l hl Y₀ Qbar :=
  ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Qbar)).lift
      (IsoAlgebra.mapOfNatIso (sfWeilCohomologyFrobenius D l hl Qbar Y₀ b))
      (sfWeilCohomology_mem D l hl Qbar Y₀ b)

/-- Mixedness means existence of a real upper weight bound, using the recorded finite
filtration by punctually pure quotients and the specified field embedding.
Source: blueprint mixedness clause (blueprint: sk-d-dl-general-weights). -/
def SfIsMixed (iota : Qbar →+* ℂ) (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) : Prop :=
  ∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota F w

/-- The cohomology sheaf in every integer degree b has mixed upper bound w+b.
Source: blueprint complex clause (blueprint: sk-d-dl-general-weights). -/
def SfComplexIsMixedOfWeightsAtMost (iota : Qbar →+* ℂ)
    (K : sfCommonStageWeilComplex D l hl Y₀ Qbar) (w : ℝ) : Prop :=
  ∀ b : ℤ, SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota
    ((sfWeilCohomology D l hl Qbar Y₀ b).obj K) (w + (b : ℝ))

private def sfPureWeightLE (iota : Qbar →+* ℂ) (w : ℝ) :
    ObjectProperty (sfCommonStageWeilSheaf D l hl Y₀ Qbar) :=
  fun F ↦ ∃ v : ℝ, v ≤ w ∧ SfIsPunctuallyPureOfWeight D l hl Qbar Y₀ iota F v

private instance sfPureWeightLE_iso (iota : Qbar →+* ℂ) (w : ℝ) :
    (sfPureWeightLE D l hl Qbar Y₀ iota w).IsClosedUnderIsomorphisms where
  of_iso {F G} e h := by
    obtain ⟨v, hv, hp⟩ := h
    refine ⟨v, hv, fun y α hα ↦ hp y α ?_⟩
    obtain ⟨L, K, ⟨a⟩, hK⟩ := hα
    exact ⟨L, K, ⟨((ObjectProperty.ι _).mapIso e) ≪≫ a⟩, hK⟩

private instance sfPureWeightLE_subobjects (iota : Qbar →+* ℂ) (w : ℝ) :
    (sfPureWeightLE D l hl Qbar Y₀ iota w).IsClosedUnderSubobjects where
  prop_of_mono {F G} f _ h := by
    obtain ⟨v, hv, hp⟩ := h
    refine ⟨v, hv, fun y α hα ↦ hp y α ?_⟩
    obtain ⟨V, φ, hlim, hcolim, hfd, hs⟩ :=
      sfPunctualSpectrumExactFibre D l hl Qbar Y₀ y
    let := hlim
    let := hcolim
    let := hfd F
    let := hfd G
    let M : FrobeniusModule Qbar :=
      ⟨V.obj F, (φ.app F).toLinearEquiv⟩
    let N : FrobeniusModule Qbar :=
      ⟨V.obj G, (φ.app G).toLinearEquiv⟩
    apply (hs G α).2
    exact FrobeniusModule.hasEigenvalue_of_injective (M := M) (N := N)
      (V.map f).hom (fun x ↦ congrArg (fun g ↦ g x) (φ.hom.naturality f).symm)
      ((ModuleCat.mono_iff_injective _).1 inferInstance) ((hs F α).1 hα)

private instance sfPureWeightLE_quotients (iota : Qbar →+* ℂ) (w : ℝ) :
    (sfPureWeightLE D l hl Qbar Y₀ iota w).IsClosedUnderQuotients where
  prop_of_epi {F G} f _ h := by
    obtain ⟨v, hv, hp⟩ := h
    refine ⟨v, hv, fun y α hα ↦ hp y α ?_⟩
    obtain ⟨V, φ, hlim, hcolim, hfd, hs⟩ :=
      sfPunctualSpectrumExactFibre D l hl Qbar Y₀ y
    let := hlim
    let := hcolim
    let := hfd F
    let := hfd G
    let M : FrobeniusModule Qbar :=
      ⟨V.obj F, (φ.app F).toLinearEquiv⟩
    let N : FrobeniusModule Qbar :=
      ⟨V.obj G, (φ.app G).toLinearEquiv⟩
    apply (hs F α).2
    exact FrobeniusModule.hasEigenvalue_of_surjective (M := M) (N := N)
      (V.map f).hom (fun x ↦ congrArg (fun g ↦ g x) (φ.hom.naturality f).symm)
      ((ModuleCat.epi_iff_surjective _).1 inferInstance) ((hs G α).1 hα)

private theorem sfMixed_iff_filtrationClosure (iota : Qbar →+* ℂ) (w : ℝ)
    (F : sfCommonStageWeilSheaf D l hl Y₀ Qbar) :
    SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota F w ↔
      (sfPureWeightLE D l hl Qbar Y₀ iota w).filtrationClosure F := by
  rw [ObjectProperty.filtrationClosure_iff]
  rfl

/-- Subobjects preserve the mixed upper bound.
Source: blueprint closure sentence (blueprint: sk-d-dl-general-weights).
Proof: intersect the finite filtration with the subobject. The new successive
quotients embed in the old pure quotients. Exact geometric stalks identify their
Frobenius eigenvalues with subsets of the old eigenvalues, retaining the same weights. -/
theorem SfIsMixedOfWeightsAtMost.of_mono (iota : Qbar →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Qbar} (i : G ⟶ F) [Mono i]
    (h : SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota F w) :
    SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota G w := by
  rw [sfMixed_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.prop_of_mono _ i h

/-- Quotients preserve the mixed upper bound.
Source: blueprint closure sentence (blueprint: sk-d-dl-general-weights).
Proof: take images of the given finite filtration under the epimorphism. The
successive quotients are quotients of the old pure quotients. Exact stalks and
Frobenius equivariance make each local spectrum a subset of the old spectrum. -/
theorem SfIsMixedOfWeightsAtMost.of_epi (iota : Qbar →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Qbar} (p : F ⟶ G) [Epi p]
    (h : SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota F w) :
    SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota G w := by
  rw [sfMixed_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.prop_of_epi _ p h

/-- Extensions preserve the mixed upper bound.
Source: blueprint closure sentence (blueprint: sk-d-dl-general-weights).
Proof: for the monomorphism G to F, first use the filtration of G inside F, then
append the inverse images of the filtration of its cokernel. The successive
quotients are exactly the original pure quotients, so each retains its bound. -/
theorem SfIsMixedOfWeightsAtMost.of_mono_cokernel (iota : Qbar →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Qbar} (i : G ⟶ F) [Mono i]
    (hG : SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota G w)
    (hQ : SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota (cokernel i) w) :
    SfIsMixedOfWeightsAtMost D l hl Qbar Y₀ iota F w := by
  rw [sfMixed_iff_filtrationClosure] at hG hQ ⊢
  exact ObjectProperty.prop_X₂_of_shortExact _
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance)
    hG hQ

end WeilConjectures
