/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential

/-! # Deformation and integration factors under an etale chart

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Steps 1--4
(blueprint: lem-pur-chart-dnc-vector-factors).

The comparison of source sections is formed through the actual Cartesian base change
of the affine diagonal projection. The normal map is induced by the extended Rees map,
then restricted to its zero fibre. Integration is transposed before its inverse is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartFactors

/-- The map e times e on self-products. Source: chart proof Step 1
(blueprint: lem-pur-chart-dnc-vector-factors). -/
def selfMap {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :=
  pullback.map h h (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
    (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) e e (𝟙 Y)
    ((Category.comp_id h).trans w.symm) ((Category.comp_id h).trans w.symm)

/-- The first projection of e times e is e after the first projection.
Source: chart proof Step 1 (blueprint: lem-pur-chart-dnc-vector-factors).
Proof: apply the first-projection equation for pullback.map. -/
theorem selfMap_fst {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    selfMap d h e w ≫ pullback.fst
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = pullback.fst h h ≫ e := by
  simp [selfMap]

/-- The intermediate map W_U -> W_A times_A U, with no shrinking or frame choice.
Source: chart proof Step 1 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def sourceLift {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y)
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :=
  pullback.lift (selfMap d h e w) (pullback.fst h h) (selfMap_fst d h e w)

/-- The intermediate map is etale and takes the diagonal to the pulled-back section.
Restricting it to the specified neighbourhood O gives the Cartesian centre square.
Source: chart proof Steps 1--2 (blueprint: lem-pur-chart-dnc-vector-factors).
Proof: identify W_A times_A U with U times_Y A. The map is 1 times e, a base change
of e, hence etale. Its separatedness follows from that of h and the affine projection;
its graph over U is closed since the target projection is separated, and projection
from the graph is a base change of the quasi-compact p_U. Thus the map is
quasi-compact. The two projections identify its diagonal composite with the
base-changed diagonal section. -/
theorem sourceLift_geometry {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    Etale (sourceLift d h e w) ∧ IsSeparated (sourceLift d h e w) ∧
      QuasiCompact (sourceLift d h e w) ∧
      pullback.diagonal h ≫ sourceLift d h e w =
        Scheme.Hom.baseChangeSection
          (pullback.fst (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
            (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
          (pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
          (pullback.diagonal_fst _) e := by
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let a := sourceLift d h e w
  let q := pullback.fst (pullback.fst p p) e ≫ pullback.snd p p
  have ha : a ≫ q = pullback.snd h h ≫ e := by
    simp [a, q, p, sourceLift, selfMap]
  have sq : IsPullback a (pullback.snd h h) q e := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ ha) ?_
    refine PullbackCone.IsLimit.mk _
      (fun c ↦ pullback.lift (c.fst ≫ pullback.snd (pullback.fst p p) e) c.snd ?_)
      ?_ ?_ ?_
    · calc
        (c.fst ≫ pullback.snd (pullback.fst p p) e) ≫ h =
            c.fst ≫ pullback.fst (pullback.fst p p) e ≫ pullback.fst p p ≫ p := by
          simpa only [p, Category.assoc, w] using
            congrArg (fun f ↦ c.fst ≫ f ≫ p)
              (pullback.condition (f := pullback.fst p p) (g := e)).symm
        _ = c.fst ≫ q ≫ p := by rw [pullback.condition]; rfl
        _ = c.snd ≫ h := by rw [← Category.assoc, c.condition, Category.assoc]; rw [w]
    · intro c
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [a, p, sourceLift, selfMap]
        · simpa [a, p, sourceLift, selfMap, q] using c.condition.symm
      · simp [a, p, sourceLift]
    · intro c
      simp
    · intro c m hm hn
      apply pullback.hom_ext
      · simpa [a, p, sourceLift] using hm =≫ pullback.snd (pullback.fst p p) e
      · simpa using hn
  have : Etale a := MorphismProperty.of_isPullback sq.flip inferInstance
  have : IsSeparated (a ≫ pullback.snd (pullback.fst p p) e) := by
    simpa [a, p, sourceLift] using inferInstanceAs (IsSeparated (pullback.fst h h))
  have : IsSeparated a := IsSeparated.of_comp a (pullback.snd (pullback.fst p p) e)
  have : QuasiCompact (a ≫ pullback.snd (pullback.fst p p) e) := by
    simpa [a, p, sourceLift] using inferInstanceAs (QuasiCompact (pullback.fst h h))
  have : QuasiCompact a := QuasiCompact.of_comp a (pullback.snd (pullback.fst p p) e)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [sourceLift, selfMap, Scheme.Hom.baseChangeSection]
  · simp [sourceLift, Scheme.Hom.baseChangeSection]

/-- Canonical ordinary section comparison a, through etale locality and inverse smooth
base change. Locality composition shows it is exactly open restriction to O followed
by the exceptional comparison for (e times e)|O. Source: chart proof Step 3
(blueprint: lem-pur-chart-dnc-vector-factors). -/
def sourceOrdinary (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  let pA := pullback.fst p p
  let g := pullback.snd pA e
  let s := Scheme.Hom.baseChangeSection pA (pullback.diagonal p)
    (pullback.diagonal_fst p) e
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (p ≫ aY)
  letI := P.noetherian (pA ≫ p ≫ aY)
  letI := P.noetherian (g ≫ h ≫ aY)
  letI := P.noetherian (pullback.fst h h ≫ h ≫ aY)
  letI := (sourceLift_geometry d h e w).1
  letI := (sourceLift_geometry d h e w).2.1
  letI := (sourceLift_geometry d h e w).2.2.1
  letI := Dnc.compactifiable P pA (p ≫ aY)
  letI := Dnc.compactifiable P g (h ≫ aY)
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aY)
  letI := Dnc.invertibleExponent P (pA ≫ p ≫ aY)
  (P.chartSectionEtaleRestriction N (sourceLift d h e w) g (pullback.fst h h)
    (pullback.lift_snd _ _ _) s (pullback.diagonal h)
      (sourceLift_geometry d h e w).2.2.2).symm ≪≫
    (Dnc.sectionBaseChange P.Coefficient d pA (IsPullback.of_hasPullback pA e)
      (pullback.diagonal p) s (Scheme.Hom.baseChangeSection_fst pA
        (pullback.diagonal p) (pullback.diagonal_fst p) e)).symm

/-- The same specified a in the pro-etale section coordinates.
Source: chart proof Step 3 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def source (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aY) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (sourceOrdinary P d h aY e w N) ≪≫
    (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst p p)
      (p ≫ aY) (pullback.diagonal p))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (Dnc.sourceComparison P d (pullback.fst p p) (p ≫ aY) (pullback.diagonal p)).symm

/-- The diagonal ideal pulls into the diagonal ideal under e times e.
Source: chart proof Steps 1--2 (blueprint: lem-pur-chart-dnc-vector-factors).
Proof: the diagonal square commutes by the two projections. Pulling a section vanishing
on the affine diagonal along e times e therefore gives one vanishing on the U diagonal.
The affine description of kernel ideals gives exactly the stated bound. -/
theorem idealCondition {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    {V : (pullback h h).AffineZariskiSite}
    {W : (pullback (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)).AffineZariskiSite}
    (H : V.1 ≤ selfMap d h e w ⁻¹ᵁ W.1) :
    ((pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)).ker.siteIdeal W).map
        ((selfMap d h e w).appLE W.1 V.1 H).hom ≤
      (pullback.diagonal h).ker.siteIdeal V := by
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  have hs : pullback.diagonal h ≫ selfMap d h e w = e ≫ pullback.diagonal p := by
    apply pullback.hom_ext <;> simp [selfMap, p]
  apply ((pullback.diagonal p).ker.ideal_map_appLE_le_ideal_comap
    (selfMap d h e w) ⟨W.1, W.2⟩ ⟨V.1, V.2⟩ H).trans
  apply Scheme.IdealSheafData.le_def.mp
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_ker, hs]
  exact Scheme.Hom.le_ker_comp _ _

/-- The actual map of extended Rees constructions, fixing t and sending a/t to e*a/t.
Source: chart proof Step 3 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def deformation {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :=
  Scheme.IdealSheafData.deformationSpaceMap (selfMap d h e w)
    (pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)).ker
    (pullback.diagonal h).ker (fun {_ _} H ↦ idealCondition d h e w H)

/-- The Rees comparison restricts to the actual zero fibre over e.
Source: chart proof Step 3 (blueprint: lem-pur-chart-dnc-vector-factors).
Proof: deformationSpaceMap_proj preserves t and lies over e on the section bases.
Precompose with the zero-fibre inclusion, whose t-coordinate is zero. This is exactly
the compatibility required by the universal property of the target zero fibre. -/
theorem normalCondition {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    ((pullback.diagonal h).ker.normalConeToDeformationSpace ≫ deformation d h e w) ≫
      Scheme.Hom.deformationSpaceProj
        (pullback.fst (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
          (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
        (pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)) =
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ e) ≫
        AffineSpace.zeroSection (ULift.{u} (Fin 1))
          (AffineSpace (ULift.{u} (Fin d)) Y) := by
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  have hm := Scheme.IdealSheafData.deformationSpaceMap_proj (selfMap d h e w)
    (pullback.diagonal p).ker (pullback.diagonal h).ker
    (fun {_ _} H ↦ idealCondition d h e w H)
    (pullback.fst p p) (pullback.fst h h) e (selfMap_fst d h e w)
  change deformation d h e w ≫ Scheme.Hom.deformationSpaceProj (pullback.fst p p)
      (pullback.diagonal p) =
    Scheme.Hom.deformationSpaceProj (pullback.fst h h) (pullback.diagonal h) ≫
      AffineSpace.map (ULift.{u} (Fin 1)) e at hm
  rw [Category.assoc, hm, ← Category.assoc,
    (Scheme.Hom.isPullback_normalConeToDeformationSpace
      (pullback.fst h h) (pullback.diagonal h)).w]
  simp [AffineSpace.zeroSection_comp_map, Category.assoc]

/-- The actual normal map v, constructed from the Rees map by the zero-fibre pullback.
Its degree-one ring map is [a] -> [e*a]; it is the specified differential, with no frame.
Source: chart proof Steps 2--3 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def normalMap {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y)
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :=
  (Scheme.Hom.isPullback_normalConeToDeformationSpace
    (pullback.fst (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
      (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
    (pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))).lift
      ((pullback.diagonal h).ker.normalConeToDeformationSpace ≫ deformation d h e w)
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ e)
      (normalCondition d h e w)

/-- Coefficientwise extended-Rees maps compose. Source: chart proof Steps 2--3
(blueprint: lem-pur-chart-dnc-vector-factors). -/
private theorem reesMap_comp {X₀ X₁ X₂ : Scheme.{u}}
    (f : X₂ ⟶ X₁) (g : X₁ ⟶ X₀)
    (I₀ : X₀.IdealSheafData) (I₁ : X₁.IdealSheafData) (I₂ : X₂.IdealSheafData)
    (hf : ∀ ⦃U₂ : X₂.AffineZariskiSite⦄ ⦃U₁ : X₁.AffineZariskiSite⦄
      (H : U₂.1 ≤ f ⁻¹ᵁ U₁.1),
      (I₁.siteIdeal U₁).map (f.appLE U₁.1 U₂.1 H).hom ≤ I₂.siteIdeal U₂)
    (hg : ∀ ⦃U₁ : X₁.AffineZariskiSite⦄ ⦃U₀ : X₀.AffineZariskiSite⦄
      (H : U₁.1 ≤ g ⁻¹ᵁ U₀.1),
      (I₀.siteIdeal U₀).map (g.appLE U₀.1 U₁.1 H).hom ≤ I₁.siteIdeal U₁)
    (hfg : ∀ ⦃U₂ : X₂.AffineZariskiSite⦄ ⦃U₀ : X₀.AffineZariskiSite⦄
      (H : U₂.1 ≤ (f ≫ g) ⁻¹ᵁ U₀.1),
      (I₀.siteIdeal U₀).map ((f ≫ g).appLE U₀.1 U₂.1 H).hom ≤ I₂.siteIdeal U₂) :
    Scheme.IdealSheafData.deformationSpaceMap f I₁ I₂ hf ≫
      Scheme.IdealSheafData.deformationSpaceMap g I₀ I₁ hg =
        Scheme.IdealSheafData.deformationSpaceMap (f ≫ g) I₀ I₂ hfg := by
  classical
  open Scheme.AffineZariskiSite in
  let C : I₂.deformationSpace.OpenCover := {
    I₀ := {q : X₂.AffineZariskiSite × X₁.AffineZariskiSite × X₀.AffineZariskiSite //
      q.1.1 ≤ f ⁻¹ᵁ q.2.1.1 ∧ q.2.1.1 ≤ g ⁻¹ᵁ q.2.2.1}
    X q := (relativeGluingData I₂.coequifibered_toReesPresheaf).functor.obj q.1.1
    f q := colimit.ι (relativeGluingData I₂.coequifibered_toReesPresheaf).functor q.1.1
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun z ↦ ?_, fun q ↦
        (relativeGluingData I₂.coequifibered_toReesPresheaf).cover.map_prop q.1.1⟩
      let x := (relativeGluingData I₂.coequifibered_toReesPresheaf).toBase z
      obtain ⟨q, hx⟩ := Pairs.exists_mem g (f x)
      obtain ⟨V, hV, hxV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        X₂.isBasis_affineOpens (U := f ⁻¹ᵁ q.1.1.1) hx
      refine ⟨⟨(⟨V, hV⟩, q.1), hle, q.2⟩, ?_⟩
      have hz : z ∈ (relativeGluingData I₂.coequifibered_toReesPresheaf).toBase ⁻¹ᵁ V :=
        hxV
      rw [toBase_preimage I₂.coequifibered_toReesPresheaf
        (⟨V, hV⟩ : X₂.AffineZariskiSite)] at hz
      exact hz }
  apply C.hom_ext
  intro q
  obtain ⟨⟨U₂, U₁, U₀⟩, Hf, Hg⟩ := q
  have Hfg : U₂.1 ≤ (f ≫ g) ⁻¹ᵁ U₀.1 := fun x hx ↦ Hg (Hf hx)
  dsimp only [C]
  simp only [Scheme.IdealSheafData.deformationSpaceMap]
  rw [Scheme.AffineZariskiSite.PullbackData.ι_comparison_assoc _ _ _ Hf,
    Scheme.AffineZariskiSite.PullbackData.ι_comparison _ _ _ Hg,
    Scheme.AffineZariskiSite.PullbackData.ι_comparison _ _ _ Hfg,
    ← Category.assoc, ← Spec.map_comp]
  have he :
      (Scheme.IdealSheafData.extendedReesPullbackData g I₀ I₁ hg).map Hg ≫
        (Scheme.IdealSheafData.extendedReesPullbackData f I₁ I₂ hf).map Hf =
          (Scheme.IdealSheafData.extendedReesPullbackData (f ≫ g) I₀ I₂ hfg).map Hfg := by
    apply CommRingCat.hom_ext
    simp only [Scheme.IdealSheafData.extendedReesPullbackData_map,
      CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [Ideal.extendedReesAlgebraMap_comp]
    simp only [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  rw [he]

/-- The same composition formula for closed-centre pairs. Source: chart proof Steps 2--3
(blueprint: lem-pur-chart-dnc-vector-factors). -/
private theorem pairMap_comp {V₀ V₁ V₂ S₀ S₁ S₂ : Scheme.{u}}
    (s₀ : S₀ ⟶ V₀) (s₁ : S₁ ⟶ V₁) (s₂ : S₂ ⟶ V₂)
    [IsClosedImmersion s₀] [IsClosedImmersion s₁] [IsClosedImmersion s₂]
    (a : V₂ ⟶ V₁) (b : S₂ ⟶ S₁) (c : V₁ ⟶ V₀) (d : S₁ ⟶ S₀)
    (w₁ : s₂ ≫ a = b ≫ s₁) (w₀ : s₁ ≫ c = d ≫ s₀)
    (w : s₂ ≫ (a ≫ c) = (b ≫ d) ≫ s₀) :
    SectionReesBaseChange.pairMap s₁ s₂ a b w₁ ≫
      SectionReesBaseChange.pairMap s₀ s₁ c d w₀ =
        SectionReesBaseChange.pairMap s₀ s₂ (a ≫ c) (b ≫ d) w := by
  apply reesMap_comp

/-- Flat Cartesian centre squares give Cartesian normal cones with their zero sections.
Source: chart proof Step 2 and section-Rees base change
(blueprint: lem-pur-chart-dnc-vector-factors). -/
private theorem normalPair_geometry {V V' S S' : Scheme.{u}}
    (g : V ⟶ S) (g' : V' ⟶ S') (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (a : V' ⟶ V) [Flat a] (b : S' ⟶ S)
    (w : s' ≫ a = b ≫ s) (hov : a ≫ g = g' ≫ b)
    (centres : IsPullback s' b a s) :
    ∃ ν : s'.ker.normalCone ⟶ s.ker.normalCone,
      ν ≫ s.ker.normalConeToDeformationSpace =
        s'.ker.normalConeToDeformationSpace ≫ SectionReesBaseChange.pairMap s s' a b w ∧
      IsPullback ν (Scheme.Hom.normalConeProj g' s') (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ ν = b ≫ s.normalConeZeroSection := by
  open Scheme.AffineZariskiSite in
  obtain ⟨ν, _, _, hν, hπ, hz, _⟩ :=
    (SectionReesBaseChange.pairMap_compatible g g' s s' a b w hov).2.2.2
  refine ⟨ν, hν, ?_, hz⟩
  let hJ : ∀ ⦃U' : V'.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄
      (H : U'.1 ≤ a ⁻¹ᵁ U.1),
      (s.ker.siteIdeal U).map (a.appLE U.1 U'.1 H).hom ≤ s'.ker.siteIdeal U' :=
    fun {U' U} H ↦ (s.ker.ideal_map_appLE_le_ideal_comap a _ _ H).trans
      (Scheme.IdealSheafData.le_def.mp
        (Scheme.Modules.closedImmersion_conormal_functorial s' s a b w).1 _)
  have : IsClosedImmersion s.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).flip inferInstance
  have he : ν = (SectionReesBaseChange.zeroPairData a s.ker s'.ker hJ).comparison _ _ := by
    apply (cancel_mono s.ker.normalConeToDeformationSpace).mp
    exact hν.trans (SectionReesBaseChange.zeroPairData_toRees a s.ker s'.ker hJ).symm
  have hn : IsPullback ν
      (Scheme.AffineZariskiSite.relativeGluingData
        s'.ker.coequifibered_toNormalConePresheaf).toBase
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase a := by
    rw [he]
    apply SectionReesBaseChange.zeroPairData_isPullback
    have hk : s'.ker = s.ker.comap a := by
      rw [← centres.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    intro x
    obtain ⟨q, hx⟩ := Scheme.AffineZariskiSite.Pairs.exists_mem a x
    refine ⟨q.1.1, q.1.2, q.2, hx, ?_⟩
    have hi : (s.ker.siteIdeal q.1.2).map (a.appLE _ _ q.2).hom =
        s'.ker.siteIdeal q.1.1 := by
      rw [hk]
      exact (Scheme.IdealSheafData.ideal_comap_appLE s.ker a _ _ q.2).symm
    exact SectionReesBaseChange.rees_flat_pushout _ _ _
      (a.flat_appLE q.1.2.2 q.1.1.2 q.2) hi
  have hb : Scheme.Hom.normalConeProj g s ≫ s =
      (Scheme.AffineZariskiSite.relativeGluingData
        s.ker.coequifibered_toNormalConePresheaf).toBase := by
    rw [← Scheme.Hom.purityNormalProjection_eq s g hs]
    exact IsClosedImmersion.lift_fac _ _ _
  have hb' : Scheme.Hom.normalConeProj g' s' ≫ s' =
      (Scheme.AffineZariskiSite.relativeGluingData
        s'.ker.coequifibered_toNormalConePresheaf).toBase := by
    rw [← Scheme.Hom.purityNormalProjection_eq s' g' hs']
    exact IsClosedImmersion.lift_fac _ _ _
  rw [← hb, ← hb'] at hn
  exact IsPullback.of_bot hn hπ centres.flip

/-- The specified differential normal map exhibits the actual pullback bundle and
preserves the augmentation sections. Source: chart proof Step 2
(blueprint: lem-pur-chart-dnc-vector-factors).
Proof: remove the complementary clopen components of U times_A U. The resulting
etale Cartesian square of centres gives flat conormal base change, with affine formula
[a] tensor y -> [e*a y]. Apply relative Spec and the homogeneous-normalized Rees
comparison. Its degree-one map is the differential de; constants and augmentations
preserve the projections and zero sections. The Rees zero-fibre universal property
identifies this map with normalMap. This includes rank zero and the empty scheme. -/
theorem normalGeometry {U Y : Scheme.{u}} (d : ℕ) (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    IsPullback (normalMap d h e w)
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h))
      (Scheme.Hom.normalConeProj
        (pullback.fst (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
          (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))
        (pullback.diagonal (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y))) e ∧
    (pullback.diagonal h).normalConeZeroSection ≫ normalMap d h e w =
      e ≫ (pullback.diagonal
        (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)).normalConeZeroSection := by
  subst h
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let pU := pullback.fst (e ≫ p) (e ≫ p)
  let pA := pullback.fst p p
  let sU := pullback.diagonal (e ≫ p)
  let sA := pullback.diagonal p
  obtain ⟨O, δ, _, hδ, sq, hq, hclosed⟩ := ChartNormalDifferential.chartGeometry p e
  let q := O.ι ≫ selfMap d (e ≫ p) e rfl
  let gO := O.ι ≫ pU
  have : IsClosedImmersion δ := hclosed
  have : Etale q := hq
  have hsO : δ ≫ gO = 𝟙 U := by
    dsimp [gO, pU]
    rw [← Category.assoc, hδ, pullback.diagonal_fst]
  have wi : δ ≫ O.ι = 𝟙 U ≫ sU := by simpa [sU] using hδ
  have si : IsPullback δ (𝟙 U) O.ι sU :=
    IsPullback.of_vert_isIso_mono ⟨wi⟩
  obtain ⟨r, hr, hri, hzr⟩ := normalPair_geometry pU gO sU δ
    (pullback.diagonal_fst _) hsO O.ι (𝟙 U) wi (by simp [gO]) si
  have : IsIso r := hri.isIso_fst_of_isIso
  have sq' : IsPullback δ e q sA := sq
  obtain ⟨v, hv, hvi, hzv⟩ := normalPair_geometry pA gO sA δ
    (pullback.diagonal_fst _) hsO q e sq'.w
    (by simp [q, gO, pU, pA, selfMap, p, Category.assoc]) sq'
  have : IsClosedImmersion sA.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace pA sA).flip inferInstance
  have hs : sU ≫ selfMap d (e ≫ p) e rfl = e ≫ sA := by
    apply pullback.hom_ext <;> simp [sU, sA, selfMap, p]
  have heq : r ≫ normalMap d (e ≫ p) e rfl = v := by
    apply (cancel_mono sA.ker.normalConeToDeformationSpace).mp
    rw [Category.assoc]
    change r ≫ ((Scheme.Hom.isPullback_normalConeToDeformationSpace pA sA).lift
      _ _ _ ≫ sA.ker.normalConeToDeformationSpace) = _
    rw [IsPullback.lift_fst, ← Category.assoc, hr, Category.assoc, hv]
    change δ.ker.normalConeToDeformationSpace ≫
      (SectionReesBaseChange.pairMap sU δ O.ι (𝟙 U) wi ≫
        SectionReesBaseChange.pairMap sA sU (selfMap d (e ≫ p) e rfl) e hs) = _
    rw [pairMap_comp sA sU δ O.ι (𝟙 U) _ e wi hs (by simpa [q] using sq'.w)]
    simp only [Category.id_comp]
    rfl
  have hπ : normalMap d (e ≫ p) e rfl ≫ Scheme.Hom.normalConeProj pA sA =
      Scheme.Hom.normalConeProj pU sU ≫ e :=
    IsPullback.lift_snd _ _ _ _
  have outer : IsPullback (r ≫ normalMap d (e ≫ p) e rfl)
      (Scheme.Hom.normalConeProj gO δ) (Scheme.Hom.normalConeProj pA sA) e := by
    rw [heq]
    exact hvi
  refine ⟨outer.of_iso (asIso r) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rfl) (by simpa using hri.w.symm) (by rfl) (by simp), ?_⟩
  calc
    sU.normalConeZeroSection ≫ normalMap d (e ≫ p) e rfl =
        (δ.normalConeZeroSection ≫ r) ≫ normalMap d (e ≫ p) e rfl := by
          rw [hzr, Category.id_comp]
    _ = e ≫ sA.normalConeZeroSection := by rw [Category.assoc, heq, hzv]

/-- The specified comparison b: inverse exceptional exchange for the actual differential
bundle square, pulled to zero and transported to pro-etale coordinates.
Source: chart proof Steps 3--4 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def normal (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let pU := pullback.fst h h
  let pA := pullback.fst p p
  let sU := pullback.diagonal h
  let sA := pullback.diagonal p
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj pA sA) :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst p)).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d pU sU (pullback.diagonal_fst h)
  letI := Dnc.normalCompactifiable P d pU (h ≫ aY) sU (pullback.diagonal_fst h)
  letI := Dnc.normalCompactifiable P d pA (p ≫ aY) sA (pullback.diagonal_fst p)
  letI := Dnc.invertibleExponent P (Scheme.Hom.normalConeProj pA sA ≫ p ≫ aY)
  Dnc.normalComparison P d pU (h ≫ aY) sU (pullback.diagonal_fst h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
      (Dnc.sectionBaseChange P.Coefficient d (Scheme.Hom.normalConeProj pA sA)
        (normalGeometry d h e w).1 sA.normalConeZeroSection sU.normalConeZeroSection
        (normalGeometry d h e w).2).symm ≪≫
    (Dnc.pullComparison P e (Dnc.normalEtale P d pA
      (p ≫ aY) sA (pullback.diagonal_fst p))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (Dnc.normalComparison P d pA (p ≫ aY) sA (pullback.diagonal_fst p)).symm

/-- The canonical comparison from the actual normal cone to its relative-Spec
conormal model, with site comparison. This contains no integration orientation.
Source: chart proof Step 4
(blueprint: lem-pur-chart-dnc-vector-factors). -/
def normalBundleComparison (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    :=
  let pU := pullback.fst h h
  let sU := pullback.diagonal h
  let π := Scheme.Hom.normalConeProj pU sU
  let z := sU.normalConeZeroSection
  letI := P.noetherian (h ≫ aY)
  letI := (chartDiagonalNormalBundle d h).1
  let F := ConormalGradedAlgebra.piece sU 1
  let M := chartNormalModel d h
  letI : SmoothOfRelativeDimension d π :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d pU sU (pullback.diagonal_fst h)
  letI := Dnc.normalCompactifiable P d pU (h ≫ aY) sU (pullback.diagonal_fst h)
  letI := P.noetherian (π ≫ h ≫ aY)
  letI := (Etale.vectorIntegration_geometry U d F).1
  letI := (Etale.vectorIntegration_geometry U d F).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π U d F) (h ≫ aY)
  letI := P.noetherian (VectorBundleZeroSection.π U d F ≫ h ≫ aY)
  Dnc.normalComparison P d pU (h ≫ aY) sU (pullback.diagonal_fst h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
      (P.chartSectionEtaleRestriction N M.hom π (VectorBundleZeroSection.π U d F)
          (chartNormal_model_exists d h).exists.choose_spec.2.1 z
          (VectorBundleZeroSection.zero U d F)
          (chartNormal_model_exists d h).exists.choose_spec.2.2)

/-- The zero-section inverse integration transpose on the actual normal bundle,
with the canonical Tate and site comparisons. The relative-Spec conormal model is
homogeneously normalized; no trivialization is chosen. Source: chart proof Step 4
(blueprint: lem-pur-chart-dnc-vector-factors). -/
def beta (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian (h ≫ aY)
  letI := (chartDiagonalNormalBundle d h).1
  normalBundleComparison P d h aY N ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
      (Etale.FiniteRingSectionDeformation.bundleOrientation P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates U (P.diagonalExponent_isUnit (h ≫ aY)) d
        (ConormalGradedAlgebra.piece (pullback.diagonal h) 1))

end WeilConjectures.PurityFiniteSetting.ChartFactors
