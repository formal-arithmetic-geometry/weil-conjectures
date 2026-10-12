module
public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex
import Sheaf.Algebra.Homology.FirstQuadrantExtendedTotalExact
import Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration
import Sheaf.CategoryTheory.DegreewiseFilteredAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.VerticalCutoffQuotientComparison
@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cutoffLift (L : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b) :
    L.truncLE (a - 1) ⟶ L.truncLE (b - 1) := by
  have : (L.truncLE (a - 1)).IsStrictlyLE (b - 1) :=
    CochainComplex.isStrictlyLE_of_le _ (a - 1) (b - 1) (by omega)
  exact inv ((L.truncLE (a - 1)).ιTruncLE (b - 1)) ≫
    CochainComplex.truncLEMap (L.ιTruncLE (a - 1)) (b - 1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma cutoffLift_ι (L : CochainComplex C ℤ) (a b : ℤ) (hab : a ≤ b) :
    cutoffLift L a b hab ≫ L.ιTruncLE (b - 1) = L.ιTruncLE (a - 1) := by
  have : (L.truncLE (a - 1)).IsStrictlyLE (b - 1) :=
    CochainComplex.isStrictlyLE_of_le _ (a - 1) (b - 1) (by omega)
  simp [cutoffLift, Category.assoc, CochainComplex.ιTruncLE_naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cutoffLiftNatTrans (a b : ℤ) (hab : a ≤ b) :
    (ComplexShape.embeddingUpIntLE (a - 1)).truncLEFunctor C ⟶
      (ComplexShape.embeddingUpIntLE (b - 1)).truncLEFunctor C where
  app L := cutoffLift L a b hab
  naturality L M f := by
    change CochainComplex.truncLEMap f (a - 1) ≫ cutoffLift M a b hab =
      cutoffLift L a b hab ≫ CochainComplex.truncLEMap f (b - 1)
    have : Mono (CochainComplex.ιTruncLE M (b - 1)) :=
      inferInstanceAs (Mono (HomologicalComplex.ιTruncLE M
        (ComplexShape.embeddingUpIntLE (b - 1))))
    apply (cancel_mono (CochainComplex.ιTruncLE M (b - 1))).1
    simp only [Category.assoc, cutoffLift_ι, CochainComplex.ιTruncLE_naturality]
    rw [← Category.assoc, cutoffLift_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def cutoffComparison (a b : ℤ) (hab : a ≤ b) :
    verticalCutoff (C := C) a ⟶ verticalCutoff b :=
  Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
    (Functor.whiskerRight (cutoffLiftNatTrans a b hab)
      (ComplexShape.embeddingUpNat.restrictionFunctor C))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma cutoffComparison_ι (a b : ℤ) (hab : a ≤ b) :
    cutoffComparison (C := C) a b hab ≫ verticalCutoffι b = verticalCutoffι a := by
  apply NatTrans.ext
  funext L
  change HomologicalComplex.restrictionMap
    (cutoffLift (L.extend ComplexShape.embeddingUpNat) a b hab) ComplexShape.embeddingUpNat ≫
      HomologicalComplex.restrictionMap
        (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (b - 1))
        ComplexShape.embeddingUpNat =
      HomologicalComplex.restrictionMap
        (CochainComplex.ιTruncLE (L.extend ComplexShape.embeddingUpNat) (a - 1))
        ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.restrictionMap_comp, cutoffLift_ι]

variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- Finite/top-endpoint cone comparison, isolating this endpoint case of the
vertical tower comparison.
Source: the columnwise smart truncation and bounded-below totalization argument in Stacks 012X.
(blueprint: lem-sp-double-complex-vertical-tower-comparison-finite)
Proof: construct the cone-to-window comparison from the short exact sequence of smart
truncations columnwise, then totalize the bounded-below quasi-isomorphism and apply homology. -/
theorem verticalTower_interval_homology_iso_finite
    (a b : ℤ) (hab : (a : EInt) ≤ (b : EInt))
    (n : ℤ) :
    Nonempty ((CochainComplex.mappingCone
      ((verticalTower K).map (homOfLE hab))).homology n ≅
      ((total (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).homology n) := by
  let f := ((cutoffComparison (C := C) a b (WithBotTop.coe_le_coe.mp hab)).mapHomologicalComplex
    (ComplexShape.up ℕ)).app K
  have hf : f ≫ ((verticalCutoffι b).mapHomologicalComplex (ComplexShape.up ℕ)).app K =
      ((verticalCutoffι a).mapHomologicalComplex (ComplexShape.up ℕ)).app K := by
    have h := congrArg (fun η ↦ (η.mapHomologicalComplex (ComplexShape.up ℕ)).app K)
      (cutoffComparison_ι (C := C) a b (WithBotTop.coe_le_coe.mp hab))
    simpa only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] using h
  have hi : Mono (((verticalCutoffι a).mapHomologicalComplex (ComplexShape.up ℕ)).app K) := by
    apply HomologicalComplex.mono_of_mono_f
    intro p
    apply HomologicalComplex.mono_of_mono_f
    intro q
    change Mono ((HomologicalComplex.ιTruncLE
      ((K.X p).extend ComplexShape.embeddingUpNat)
      (ComplexShape.embeddingUpIntLE (a - 1))).f (ComplexShape.embeddingUpNat.f q))
    infer_instance
  have : Mono f := mono_of_mono_fac hf
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hT := shortExact_extended_total S hS
  let T := ShortComplex.mk
    (HomologicalComplex.extendMap (total.map S.f (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (total.map S.g (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, ← total.map_comp, S.zero,
      total.map_zero, HomologicalComplex.extendMap_zero])
  have ht : T.f = (verticalTower K).map (homOfLE hab) := by
    have := (verticalTower_inclusion_mono_and_factors K (b : EInt)).1
    apply (cancel_mono (verticalTowerι K (b : EInt))).1
    rw [show (verticalTower K).map (homOfLE hab) = verticalTowerMap K hab from rfl,
      verticalTowerMap_ι]
    change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ = _
    rw [← HomologicalComplex.extendMap_comp, ← total.map_comp, hf]
    rfl
  have hcone : QuasiIso (CochainComplex.mappingCone.descShortComplex T) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hT
  obtain ⟨q, hq⟩ := verticalCutoff_cokernel_column_comparison K a b
    (WithBotTop.coe_le_coe.mp hab) f hf
  let qext := HomologicalComplex.extendMap (total.map q (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  have hqext : QuasiIso qext := by
    obtain ⟨F, hbounds, hneg, hgraded⟩ := firstQuadrant_vertical_cone_filtration q
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic qext).mpr
    apply degreewiseFiltered_acyclic (CochainComplex.mappingCone qext) F
      (fun n ↦ ⟨0, n + 2, hbounds n⟩)
    intro p n
    apply ((F.gradedPiece p).exactAt_iff_isZero_homology n).mpr
    by_cases hp : p < 0
    · exact hneg p n hp
    · obtain ⟨e⟩ := hgraded p n (by omega)
      have : QuasiIso (q.f p.toNat) := hq p.toNat
      have hcol := (CochainComplex.mappingCone.quasiIso_iff_acyclic
        (HomologicalComplex.extendMap (q.f p.toNat) ComplexShape.embeddingUpNat)).mp
          (inferInstance : QuasiIso _)
      exact e.isZero_iff.mpr (hcol (n - p)).isZero_homology
  have hc : IsIso (HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.descShortComplex T) n) := by infer_instance
  have hw : IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex.extendMap (total.map q (ComplexShape.up ℕ))
      ComplexShape.embeddingUpNat) n) := by infer_instance
  rw [← ht]
  exact ⟨asIso (HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.descShortComplex T) n) ≪≫
    asIso (HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (total.map q (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat) n)⟩
end HomologicalComplex₂
