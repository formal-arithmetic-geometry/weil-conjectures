module

public import Sheaf.Paper.ChartDncVectorFactors
public import Sheaf.Paper.PuritySectionEtaleRestriction
public import Sheaf.Paper.StandingExceptionalComposition
import all Sheaf.Paper.SectionReesBaseChangeEtale
import all Sheaf.Paper.ChartNormalDifferential

/-! # Canonical comparisons between smooth etale chart sources

Source: blueprint latest, orientation-charts proof Steps 1--4 and composition-coherence
proof Step 1 (blueprint: def-pur-general-chart-comparisons).

These are the existing affine-chart constructions with an arbitrary smooth chart target:
the two-square counit comparison and the actual zero fibre of the extended-Rees map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- The map e times e on self-products. Source: chart proof Step 1
(blueprint: def-pur-general-chart-comparisons). -/
def selfMap {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  pullback.map h h g
    g e e (𝟙 Y)
    ((Category.comp_id h).trans w.symm) ((Category.comp_id h).trans w.symm)

/-- The first projection of e times e is e after the first projection.
Source: chart proof Step 1 (blueprint: def-pur-general-chart-comparisons).
Proof: apply the first-projection equation for pullback.map. -/
theorem selfMap_fst {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    (e : U ⟶ X)
    (w : e ≫ g = h) :
    selfMap d g h e w ≫ pullback.fst
      g
      g = pullback.fst h h ≫ e := by
  simp [selfMap, pullback.map]

/-- The intermediate map W_U -> W_A times_A U, with no shrinking or frame choice.
Source: chart proof Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def sourceLift {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  pullback.lift (selfMap d g h e w) (pullback.fst h h) (selfMap_fst d g h e w)

/-- The intermediate map is etale and takes the diagonal to the pulled-back section.
Restricting it to the specified neighbourhood O gives the Cartesian centre square.
Source: chart proof Steps 1--2 (blueprint: def-pur-general-chart-comparisons).
Proof: identify W_A times_A U with U times_Y A. The map is 1 times e, a base change
of e, hence etale. Its separatedness follows from that of h and the affine projection;
its graph over U is closed since the target projection is separated, and projection
from the graph is a base change of the quasi-compact p_U. Thus the map is
quasi-compact. The two projections identify its diagonal composite with the
base-changed diagonal section. -/
theorem sourceLift_geometry {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h) :
    Etale (sourceLift d g h e w) ∧ IsSeparated (sourceLift d g h e w) ∧
      QuasiCompact (sourceLift d g h e w) ∧
      pullback.diagonal h ≫ sourceLift d g h e w =
        Scheme.Hom.baseChangeSection
          (pullback.fst g
            g)
          (pullback.diagonal g)
          (pullback.diagonal_fst _) e := by
  have sq : IsPullback (sourceLift d g h e w) (pullback.snd h h)
      (pullback.fst (pullback.fst g g) e ≫ pullback.snd g g) e := by
    apply IsPullback.mk'
    · simp only [sourceLift, pullback.lift_fst_assoc, selfMap, pullback.lift_snd]
    · intro T a b hab hs
      apply pullback.hom_ext
      · simpa only [Category.assoc, sourceLift, pullback.lift_snd] using
          hab =≫ pullback.snd (pullback.fst g g) e
      · exact hs
    · intro T a b hab
      have hw : (a ≫ pullback.snd (pullback.fst g g) e) ≫ h = b ≫ h := by
        calc
          _ = (a ≫ pullback.snd (pullback.fst g g) e) ≫ e ≫ g := by rw [w]
          _ = (a ≫ pullback.fst (pullback.fst g g) e) ≫ pullback.fst g g ≫ g := by
            simp only [Category.assoc]
            rw [← pullback.condition_assoc]
          _ = (a ≫ pullback.fst (pullback.fst g g) e) ≫ pullback.snd g g ≫ g := by
            rw [pullback.condition]
          _ = b ≫ e ≫ g := by simpa only [Category.assoc] using hab =≫ g
          _ = b ≫ h := by rw [w]
      refine ⟨pullback.lift (a ≫ pullback.snd (pullback.fst g g) e) b hw, ?_,
        pullback.lift_snd _ _ _⟩
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, sourceLift, pullback.lift_fst, selfMap]
          rw [pullback.lift_fst_assoc]
          exact (congrArg (a ≫ ·)
            (pullback.condition (f := pullback.fst g g) (g := e))).symm
        · simpa only [Category.assoc, sourceLift, pullback.lift_fst, selfMap,
            pullback.lift_snd, pullback.lift_snd_assoc] using hab.symm
      · simp only [sourceLift, Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have het : Etale (sourceLift d g h e w) :=
    MorphismProperty.of_isPullback sq.flip inferInstance
  have hov : sourceLift d g h e w ≫
      pullback.snd (pullback.fst g g) e = pullback.fst h h :=
    pullback.lift_snd _ _ _
  have hsep : IsSeparated (sourceLift d g h e w) := by
    have : IsSeparated (sourceLift d g h e w ≫
        pullback.snd (pullback.fst g g) e) := by rw [hov]; infer_instance
    exact IsSeparated.of_comp _ (pullback.snd (pullback.fst g g) e)
  have hqc : QuasiCompact (sourceLift d g h e w) := by
    have : QuasiCompact (sourceLift d g h e w ≫
        pullback.snd (pullback.fst g g) e) := by rw [hov]; infer_instance
    exact QuasiCompact.of_comp _ (pullback.snd (pullback.fst g g) e)
  refine ⟨het, hsep, hqc, ?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [sourceLift, selfMap, Scheme.Hom.baseChangeSection]
  · simp only [Category.assoc, sourceLift, pullback.lift_snd,
      pullback.diagonal_fst, Scheme.Hom.baseChangeSection, pullback.lift_snd]

/-- Canonical ordinary section comparison a, through etale locality and inverse smooth
base change. Locality composition shows it is exactly open restriction to O followed
by the exceptional comparison for (e times e)|O. Source: chart proof Step 3
(blueprint: def-pur-general-chart-comparisons). -/
def sourceOrdinary (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := g
  let pA := pullback.fst p p
  let g₀ := pullback.snd pA e
  let s := Scheme.Hom.baseChangeSection pA (pullback.diagonal p)
    (pullback.diagonal_fst p) e
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (p ≫ aY)
  letI := P.noetherian (pA ≫ p ≫ aY)
  letI := P.noetherian (g₀ ≫ h ≫ aY)
  letI := P.noetherian (pullback.fst h h ≫ h ≫ aY)
  letI := (sourceLift_geometry d g h e w).1
  letI := (sourceLift_geometry d g h e w).2.1
  letI := (sourceLift_geometry d g h e w).2.2.1
  letI := Dnc.compactifiable P pA (p ≫ aY)
  letI := Dnc.compactifiable P g₀ (h ≫ aY)
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aY)
  letI := Dnc.invertibleExponent P (pA ≫ p ≫ aY)
  (P.chartSectionEtaleRestriction N (sourceLift d g h e w) g₀ (pullback.fst h h)
    (pullback.lift_snd _ _ _) s (pullback.diagonal h)
      (sourceLift_geometry d g h e w).2.2.2).symm ≪≫
    (Dnc.sectionBaseChange P.Coefficient d pA (IsPullback.of_hasPullback pA e)
      (pullback.diagonal p) s (Scheme.Hom.baseChangeSection_fst pA
        (pullback.diagonal p) (pullback.diagonal_fst p) e)).symm

/-- The same specified a in the pro-etale section coordinates.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def source (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := g
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aY) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (sourceOrdinary P d g h aY e w N) ≪≫
    (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst p p)
      (p ≫ aY) (pullback.diagonal p))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (Dnc.sourceComparison P d (pullback.fst p p) (p ≫ aY) (pullback.diagonal p)).symm

/-- The diagonal ideal pulls into the diagonal ideal under e times e.
Source: chart proof Steps 1--2 (blueprint: def-pur-general-chart-comparisons).
Proof: the diagonal square commutes by the two projections. Pulling a section vanishing
on the affine diagonal along e times e therefore gives one vanishing on the U diagonal.
The affine description of kernel ideals gives exactly the stated bound. -/
theorem idealCondition {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ X)
    (w : e ≫ g = h)
    {V : (pullback h h).AffineZariskiSite}
    {W : (pullback g
      g).AffineZariskiSite}
    (H : V.1 ≤ selfMap d g h e w ⁻¹ᵁ W.1) :
    ((pullback.diagonal g).ker.siteIdeal W).map
        ((selfMap d g h e w).appLE W.1 V.1 H).hom ≤
      (pullback.diagonal h).ker.siteIdeal V := by
  apply ((pullback.diagonal g).ker.ideal_map_appLE_le_ideal_comap
    (selfMap d g h e w) ⟨W.1, W.2⟩ ⟨V.1, V.2⟩ H).trans
  apply Scheme.IdealSheafData.le_def.mp
  rw [Scheme.IdealSheafData.comap_le_ker_iff]
  have he : pullback.diagonal h ≫ selfMap d g h e w = e ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [selfMap]
  rw [he]
  exact Scheme.Hom.le_ker_comp e (pullback.diagonal g)

/-- The actual map of extended Rees constructions, fixing t and sending a/t to e*a/t.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def deformation {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  Scheme.IdealSheafData.deformationSpaceMap (selfMap d g h e w)
    (pullback.diagonal g).ker
    (pullback.diagonal h).ker (fun {_ _} H ↦ idealCondition d g h e w H)

/-- The Rees comparison restricts to the actual zero fibre over e.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons).
Proof: deformationSpaceMap_proj preserves t and lies over e on the section bases.
Precompose with the zero-fibre inclusion, whose t-coordinate is zero. This is exactly
the compatibility required by the universal property of the target zero fibre. -/
theorem normalCondition {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ X)
    (w : e ≫ g = h) :
    ((pullback.diagonal h).ker.normalConeToDeformationSpace ≫ deformation d g h e w) ≫
      Scheme.Hom.deformationSpaceProj
        (pullback.fst g
          g)
        (pullback.diagonal g) =
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ e) ≫
        AffineSpace.zeroSection (ULift.{u} (Fin 1))
          (X) := by
  have hp : deformation d g h e w ≫
      Scheme.Hom.deformationSpaceProj (pullback.fst g g) (pullback.diagonal g) =
      Scheme.Hom.deformationSpaceProj (pullback.fst h h) (pullback.diagonal h) ≫
        AffineSpace.map (ULift.{u} (Fin 1)) e := by
    exact Scheme.IdealSheafData.deformationSpaceMap_proj _ _ _ _ _ _ _
      (selfMap_fst d g h e w)
  rw [Category.assoc, hp, ← Category.assoc,
    (Scheme.Hom.isPullback_normalConeToDeformationSpace
      (pullback.fst h h) (pullback.diagonal h)).w,
    Category.assoc, AffineSpace.zeroSection_comp_map, ← Category.assoc]

/-- The actual normal map v, constructed from the Rees map by the zero-fibre pullback.
Its degree-one ring map is [a] -> [e*a]; it is the specified differential, with no frame.
Source: chart proof Steps 2--3 (blueprint: def-pur-general-chart-comparisons). -/
def normalMap {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  (Scheme.Hom.isPullback_normalConeToDeformationSpace
    (pullback.fst g
      g)
    (pullback.diagonal g)).lift
      ((pullback.diagonal h).ker.normalConeToDeformationSpace ≫ deformation d g h e w)
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ e)
      (normalCondition d g h e w)

private theorem rees_open_comp {V V' W S T : Scheme.{u}}
    (s : S ⟶ V) (s' : S ⟶ V') (t : T ⟶ W)
    [IsClosedImmersion s] [IsClosedImmersion s'] [IsClosedImmersion t]
    (j : V' ⟶ V) [IsOpenImmersion j] (m : V ⟶ W) (b : S ⟶ T)
    (w : s' ≫ j = s) (v : s ≫ m = b ≫ t) :
    SectionReesBaseChange.pairMap s s' j (𝟙 S) (by simpa using w) ≫
        SectionReesBaseChange.pairMap t s m b v =
      SectionReesBaseChange.pairMap t s' (j ≫ m) b
        (by rw [← Category.assoc, w, v]) := by
  open Scheme.AffineZariskiSite Scheme.IdealSheafData in
  apply hom_ext_of_le_preimage (j ≫ m) s'.ker.coequifibered_toReesPresheaf
  intro P Q hPQ
  let R := imageSite j P
  have hPR : P.1 ≤ j ⁻¹ᵁ R.1 := (j.preimage_image_eq P.1).ge
  have hRQ : R.1 ≤ m ⁻¹ᵁ Q.1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPQ hx
  unfold SectionReesBaseChange.pairMap Scheme.IdealSheafData.deformationSpaceMap
  simp only [PullbackData.ι_comparison_assoc _ _ _ hPR,
    PullbackData.ι_comparison _ _ _ hRQ,
    PullbackData.ι_comparison _ _ _ hPQ, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  simp only [Scheme.IdealSheafData.extendedReesPullbackData_map]
  generalize_proofs h₁ h₂ h₃
  change ((s.ker.siteIdeal R).extendedReesAlgebraMap (j.appLE R.1 P.1 hPR).hom
    (s'.ker.siteIdeal P) (by assumption)).comp
      ((t.ker.siteIdeal Q).extendedReesAlgebraMap (m.appLE Q.1 R.1 hRQ).hom
        (s.ker.siteIdeal R) (by assumption)) =
    (t.ker.siteIdeal Q).extendedReesAlgebraMap ((j ≫ m).appLE Q.1 P.1 hPQ).hom
      (s'.ker.siteIdeal P) (by assumption)
  rw [Ideal.extendedReesAlgebraMap_comp]
  congr 1
  exact congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_comp_appLE j m Q.1 R.1 P.1 hRQ hPR)


private def pairNormal {V V' S S' : Scheme.{u}} (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (f : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ f = b ≫ s) : s'.ker.normalCone ⟶ s.ker.normalCone :=
  (SectionReesBaseChange.zeroPairData f s.ker s'.ker
    (fun {U' U} hU ↦
      (s.ker.ideal_map_appLE_le_ideal_comap f ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU).trans
        (Scheme.IdealSheafData.le_def.mp
          (Scheme.Modules.closedImmersion_conormal_functorial s' s f b w).1
            ⟨U'.1, U'.2⟩))).comparison _ _

private theorem pairNormal_toRees {V V' S S' : Scheme.{u}}
    (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s'] (f : V' ⟶ V) (b : S' ⟶ S)
    (w : s' ≫ f = b ≫ s) :
    pairNormal s s' f b w ≫ s.ker.normalConeToDeformationSpace =
      s'.ker.normalConeToDeformationSpace ≫ SectionReesBaseChange.pairMap s s' f b w :=
  SectionReesBaseChange.zeroPairData_toRees f s.ker s'.ker _

private theorem pairNormal_flat {V V' S S' : Scheme.{u}}
    (g : V ⟶ S) (g' : V' ⟶ S') (s : S ⟶ V) (s' : S' ⟶ V')
    [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ g = 𝟙 S) (hs' : s' ≫ g' = 𝟙 S')
    (f : V' ⟶ V) [Flat f] (b : S' ⟶ S)
    (w : s' ≫ f = b ≫ s) (hover : f ≫ g = g' ≫ b)
    (sq : IsPullback s' b f s) :
    IsPullback (pairNormal s s' f b w) (Scheme.Hom.normalConeProj g' s')
      (Scheme.Hom.normalConeProj g s) b ∧
      s'.normalConeZeroSection ≫ pairNormal s s' f b w = b ≫ s.normalConeZeroSection := by
  open Scheme.AffineZariskiSite in
  have hn : IsPullback (pairNormal s s' f b w)
      (relativeGluingData s'.ker.coequifibered_toNormalConePresheaf).toBase
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase f := by
    unfold pairNormal
    apply SectionReesBaseChange.zeroPairData_isPullback
    have hk : s'.ker = s.ker.comap f := by
      rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    intro x
    obtain ⟨W, hW, hxW, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      V.isBasis_affineOpens (U := ⊤) (show f x ∈ (⊤ : V.Opens) from trivial)
    obtain ⟨W', hW', hxW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      V'.isBasis_affineOpens (U := f ⁻¹ᵁ W) hxW
    refine ⟨⟨W', hW'⟩, ⟨W, hW⟩, hle, hxW', ?_⟩
    have he : s'.ker.siteIdeal ⟨W', hW'⟩ =
        (s.ker.siteIdeal ⟨W, hW⟩).map (f.appLE W W' hle).hom := by
      rw [Scheme.IdealSheafData.siteIdeal, hk,
        Scheme.IdealSheafData.ideal_comap_appLE s.ker f ⟨W, hW⟩ ⟨W', hW'⟩ hle]
    change IsPushout _ _ _ (CommRingCat.ofHom
      ((s.ker.siteIdeal ⟨W, hW⟩).extendedReesAlgebraMap (f.appLE W W' hle).hom
        (s'.ker.siteIdeal ⟨W', hW'⟩) _))
    generalize_proofs hbound
    dsimp only [Scheme.IdealSheafData.toReesPresheaf]
    generalize s'.ker.siteIdeal ⟨W', hW'⟩ = J at he hbound ⊢
    subst J
    exact Ideal.isPushout_extendedReesAlgebraMap_of_flat _ (f.flat_appLE hW hW' hle) _
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
  have hp : pairNormal s s' f b w ≫ Scheme.Hom.normalConeProj g s =
      Scheme.Hom.normalConeProj g' s' ≫ b := by
    unfold Scheme.Hom.normalConeProj
    rw [← Category.assoc, hn.w, Category.assoc, hover, Category.assoc]
  refine ⟨?_, ?_⟩
  · rw [← hb, ← hb'] at hn
    exact IsPullback.of_bot hn hp sq.flip
  · have : IsClosedImmersion s.ker.normalConeToDeformationSpace :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).flip inferInstance
    obtain ⟨_, _, _, ν, l, _, hν, _, hz, _⟩ :=
      SectionReesBaseChange.pairMap_compatible g g' s s' f b w hover
    have he : pairNormal s s' f b w = ν := by
      apply (cancel_mono s.ker.normalConeToDeformationSpace).mp
      exact (SectionReesBaseChange.zeroPairData_toRees f s.ker s'.ker _).trans hν.symm
    rw [he]
    exact hz

/-- The specified differential normal map exhibits the actual pullback bundle and
preserves the augmentation sections. Source: chart proof Step 2
(blueprint: def-pur-general-chart-comparisons).
Proof: remove the complementary clopen components of U times_A U. The resulting
etale Cartesian square of centres gives flat conormal base change, with affine formula
[a] tensor y -> [e*a y]. Apply relative Spec and the homogeneous-normalized Rees
comparison. Its degree-one map is the differential de; constants and augmentations
preserve the projections and zero sections. The Rees zero-fibre universal property
identifies this map with normalMap. This includes rank zero and the empty scheme. -/
theorem normalGeometry {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h) :
    IsPullback (normalMap d g h e w)
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h))
      (Scheme.Hom.normalConeProj
        (pullback.fst g
          g)
        (pullback.diagonal g)) e ∧
    (pullback.diagonal h).normalConeZeroSection ≫ normalMap d g h e w =
      e ≫ (pullback.diagonal
        g).normalConeZeroSection := by
  subst h
  let m := selfMap d g (e ≫ g) e rfl
  let sU := pullback.diagonal (e ≫ g)
  let sX := pullback.diagonal g
  let pU := pullback.fst (e ≫ g) (e ≫ g)
  let pX := pullback.fst g g
  have hm : m ≫ pX = pU ≫ e := selfMap_fst d g (e ≫ g) e rfl
  have hw : sU ≫ m = e ≫ sX := by
    apply pullback.hom_ext <;> simp [m, sU, sX, selfMap]
  obtain ⟨O, δ, _, hδ, hcart, het, hclosed⟩ := ChartNormalDifferential.chartGeometry g e
  have : IsClosedImmersion δ := hclosed
  have : Etale (O.ι ≫ m) := het
  have hR : IsPullback δ (𝟙 U) O.ι sU :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hδ⟩
  have hδp : δ ≫ (O.ι ≫ pU) = 𝟙 U := by
    rw [← Category.assoc, hδ]
    exact pullback.diagonal_fst _
  have hRover : O.ι ≫ pU = (O.ι ≫ pU) ≫ 𝟙 U := (Category.comp_id _).symm
  have hQover : (O.ι ≫ m) ≫ pX = (O.ι ≫ pU) ≫ e := by
    simp only [Category.assoc, hm]
  have hQ : δ ≫ (O.ι ≫ m) = e ≫ sX := hcart.w
  let nR := pairNormal sU δ O.ι (𝟙 U) hR.w
  let nQ := pairNormal sX δ (O.ι ≫ m) e hQ
  have hNR := pairNormal_flat pU (O.ι ≫ pU) sU δ
    (pullback.diagonal_fst _) hδp O.ι (𝟙 U) hR.w hRover hR
  have hNQ := pairNormal_flat pX (O.ι ≫ pU) sX δ
    (pullback.diagonal_fst _) hδp (O.ι ≫ m) e hQ hQover hcart
  have : IsIso nR := hNR.1.isIso_fst_of_isIso
  have : IsClosedImmersion sX.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace pX sX).flip inferInstance
  have hcomp : nR ≫ normalMap d g (e ≫ g) e rfl = nQ := by
    apply (cancel_mono sX.ker.normalConeToDeformationSpace).mp
    rw [Category.assoc, normalMap, IsPullback.lift_fst,
      ← Category.assoc, pairNormal_toRees, Category.assoc, pairNormal_toRees]
    have he : SectionReesBaseChange.pairMap sU δ O.ι (𝟙 U) hR.w ≫
        deformation d g (e ≫ g) e rfl =
        SectionReesBaseChange.pairMap sX δ (O.ι ≫ m) e hQ := by
      exact rees_open_comp sU δ sX O.ι m e hδ hw
    rw [he]
  refine ⟨?_, ?_⟩
  · apply hNQ.1.of_iso (asIso nR) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa using hcomp.symm
    · simpa using hNR.1.w.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp
  · have hzR : δ.normalConeZeroSection ≫ nR = sU.normalConeZeroSection := by
      simpa using hNR.2
    rw [← hzR, Category.assoc, hcomp]
    exact hNQ.2

/-- The specified comparison b: inverse exceptional exchange for the actual differential
bundle square, pulled to zero and transported to pro-etale coordinates.
Source: chart proof Steps 3--4 (blueprint: def-pur-general-chart-comparisons). -/
def normal (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h) :=
  let p := g
  let pU := pullback.fst h h
  let pA := pullback.fst p p
  let sU := pullback.diagonal h
  let sA := pullback.diagonal p
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
        (normalGeometry d g h e w).1 sA.normalConeZeroSection sU.normalConeZeroSection
        (normalGeometry d g h e w).2).symm ≪≫
    (Dnc.pullComparison P e (Dnc.normalEtale P d pA
      (p ≫ aY) sA (pullback.diagonal_fst p))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (Dnc.normalComparison P d pA (p ≫ aY) sA (pullback.diagonal_fst p)).symm


/-- Specialization to the already published affine-chart constructions, including
their actual self-product, Rees and normal maps and their ordinary/site transports.
Source: orientation-charts proof Steps 1--4
(blueprint: def-pur-general-chart-comparisons).

Proof: unfold the two self-product maps; they are the same pullback.map. The
first-projection proofs are equal by proof irrelevance, hence the pullback lifts
are equal. The diagonal-ideal bounds are proofs of the same proposition, so the
extended-Rees maps agree. Their zero-fibre compatibility proofs are likewise
equal, and the zero-fibre pullback lifts agree. Substitute these equalities in
the two section-base-change squares. The geometry witnesses are proof irrelevant;
both ordinary source comparisons are therefore the same inverse counit locality
followed by the same inverse smooth base change. The site-comparison factors
are identical. The normal comparisons similarly use the same actual normal
square and zero sections, so their smooth exchanges and site transports agree. -/
theorem affine_specialization (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
    letI : SmoothOfRelativeDimension d p := by
      simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
    selfMap d p h e w = ChartFactors.selfMap d h e w ∧
    sourceLift d p h e w = ChartFactors.sourceLift d h e w ∧
    deformation d p h e w = ChartFactors.deformation d h e w ∧
    normalMap d p h e w = ChartFactors.normalMap d h e w ∧
    sourceOrdinary P d p h aY e w N = ChartFactors.sourceOrdinary P d h aY e w N ∧
    source P d p h aY e w N = ChartFactors.source P d h aY e w N ∧
    normal P d p h aY e w = ChartFactors.normal P d h aY e w := by
  dsimp only
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The existing dualizing object with Nagata supplied by its finite-type domain.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def omega (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := Dnc.compactifiable P g aY
  P.diagonalDualizing g

/-- The counit-normalized exceptional/etale comparison, transported through the
published comparison-unit isomorphisms. No orientation enters this definition.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def epsilon (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    omega P (e ≫ g) aY ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.obj
        (omega P g aY) :=
  letI := P.noetherian aY
  letI := P.noetherian (g ≫ aY)
  letI := P.noetherian ((e ≫ g) ≫ aY)
  letI := Dnc.compactifiable P g aY
  letI := Dnc.compactifiable P (e ≫ g) aY
  P.diagonalDualizingComparison (e ≫ g) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.diagonalEtaleLocality N e g).symm ≪≫
    (Dnc.pullComparison P e (P.diagonalOrdinaryDualizing g)).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison g).symm

/-- The specific pur9 composition morphism at the coefficient unit. Structure maps
are the displayed composites; the unit is the existing bounded constructible object.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def composition (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e] :=
  letI : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨g ≫ aY⟩
  letI : U.Over (Spec (.of P.field.k)) := ⟨e ≫ (g ≫ aY)⟩
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aY)
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aY)
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ aY))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ aY))
  letI : LocallyOfFiniteType (U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (e ≫ (g ≫ aY)))
  letI : QuasiCompact (U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (e ≫ (g ≫ aY)))
  letI : e.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  ProEtale.standingExceptionalComposition P e g (P.chartCoefficientUnit Y)

/-- The canonical etale identification at omega_g, including the site-comparison unit.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def rho (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aY
  letI := P.noetherian (g ≫ aY)
  letI := P.noetherian ((e ≫ g) ≫ aY)
  letI := Dnc.compactifiable P g aY
  letI := Dnc.compactifiable P e (g ≫ aY)
  (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) e).mapIso
      (P.diagonalDualizingComparison g) ≪≫
    P.chartEtaleIdentification e N (P.diagonalOrdinaryDualizing g)
      (Etale.plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} P.Coefficient)
        g _ (P.diagonalUnitPlus Y)) ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (P.diagonalDualizingComparison g).symm

/-- An affine etale coordinate chart over V. Affineness is part of the item's domain.
Source: orientation-charts proof Steps 1--4
(blueprint: def-pur-general-chart-comparisons). -/
structure Chart (V : Scheme.{u}) (d : ℕ) where
  X : Scheme.{u}
  affine : IsAffine X
  coord : X ⟶ AffineSpace (ULift.{u} (Fin d)) V
  etale : Etale coord

attribute [instance] Chart.affine Chart.etale

/-- The structure map of the chart is the specified coordinate composite.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def Chart.proj {V : Scheme.{u}} {d : ℕ} (C : Chart V d) :=
  C.coord ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V)

/-- Finite type of the coordinate composite, using the existing morphism instances.
Source: chart domain (blueprint: def-pur-general-chart-comparisons). -/
instance Chart.locallyOfFiniteType {V : Scheme.{u}} {d : ℕ} (C : Chart V d) :
    LocallyOfFiniteType C.proj :=
  inferInstanceAs (LocallyOfFiniteType
    (C.coord ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V)))

/-- Etale composition with affine projection has the prescribed pure dimension.
Source: chart proof hypotheses (blueprint: def-pur-general-chart-comparisons).
Proof: an etale morphism is smooth of dimension zero, and the affine projection
has relative dimension d. The smooth composition theorem gives 0+d=d. -/
theorem Chart.smooth {V : Scheme.{u}} {d : ℕ} (C : Chart V d) :
    SmoothOfRelativeDimension d C.proj := by
  have : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) V ↘ V) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) V
  simpa only [Chart.proj, Nat.zero_add] using
    (smoothOfRelativeDimension_comp (n := 0) (m := d)
      C.coord (AffineSpace (ULift.{u} (Fin d)) V ↘ V))

attribute [instance] Chart.smooth

/-- An etale map between affine chart sources over V. No orientation is specified.
Source: composition-coherence proof Step 1
(blueprint: def-pur-general-chart-comparisons). -/
structure Map {V : Scheme.{u}} {d : ℕ} (C B : Chart V d) where
  hom : C.X ⟶ B.X
  etale : Etale hom
  over_eq : hom ≫ B.proj = C.proj

attribute [instance] Map.etale

/-- Identity chart map. Source: composition-coherence Step 1
(blueprint: def-pur-general-chart-comparisons). -/
def Map.id {V : Scheme.{u}} {d : ℕ} (C : Chart V d) : Map C C where
  hom := 𝟙 C.X
  etale := inferInstance
  over_eq := Category.id_comp _

/-- Pasting chart maps. Source: composition-coherence Step 1
(blueprint: def-pur-general-chart-comparisons). -/
def Map.comp {V : Scheme.{u}} {d : ℕ} {C B A : Chart V d}
    (v : Map C B) (e : Map B A) : Map C A where
  hom := v.hom ≫ e.hom
  etale := inferInstance
  over_eq := (Category.assoc _ _ _).trans
    ((congrArg (fun f ↦ v.hom ≫ f) e.over_eq).trans v.over_eq)

/-- The standard affine projection as a chart, including d=0.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def standard (V : Scheme.{u}) [IsAffine V] (d : ℕ) : Chart V d where
  X := AffineSpace (ULift.{u} (Fin d)) V
  affine := inferInstance
  coord := 𝟙 _
  etale := inferInstance

/-- The coordinate map from any chart to the standard chart.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def coordinate {V : Scheme.{u}} [IsAffine V] {d : ℕ} (C : Chart V d) :
    Map C (standard V d) where
  hom := C.coord
  etale := C.etale
  over_eq := rfl

/-- The diagonal section invariant of an affine chart source.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def sectionObject (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) :=
  Dnc.sourceSection P d (pullback.fst C.proj C.proj) (C.proj ≫ aV)
    (pullback.diagonal C.proj)

/-- The invariant of the actual normal bundle of the chart diagonal.
Source: chart proof Step 2 (blueprint: def-pur-general-chart-comparisons). -/
def normalSection (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) :=
  Dnc.normalSection P d (pullback.fst C.proj C.proj) (C.proj ≫ aV)
    (pullback.diagonal C.proj) (pullback.diagonal_fst C.proj)

/-- The specified diagonal base-change isomorphism.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def alpha (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) := P.chartDiagonalAlpha d C.proj aV

/-- The unique DNC comparison normalized at one, with no orientation input.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def delta (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C : Chart V d) :=
  letI : IsSeparated (C.proj ≫ aV) := inferInstance
  (Dnc.existsUnique_dncInvariance P d (pullback.fst C.proj C.proj) (C.proj ≫ aV)
    (pullback.diagonal C.proj) (pullback.diagonal_fst C.proj)).exists.choose

/-- The source counit comparison for a chart map, with target a literal pullback.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def q (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  source P d B.proj C.proj aV e.hom e.over_eq N

/-- The actual differential normal-bundle comparison for a chart map.
Source: chart proof Steps 2--3 (blueprint: def-pur-general-chart-comparisons). -/
def r (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B) :=
  normal P d B.proj C.proj aV e.hom e.over_eq

/-- Congruence of the existing dualizing object under equality of its structure map.
Source: canonical composition constraints (blueprint: def-pur-general-chart-comparisons). -/
def omegaCongr (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    {f g : U ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (w : f = g) : omega P f aY ≅ omega P g aY :=
  eqToIso (by cases w; rfl)

/-- Epsilon for a chart map, with the displayed equality of structure morphisms.
Source: chart proof Step 3 (blueprint: def-pur-general-chart-comparisons). -/
def eps (P : PurityFiniteSetting.{u}) {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := Dnc.compactifiable P C.proj aV
  letI := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  omegaCongr P aV e.over_eq.symm ≪≫
    epsilon P B.proj aV e.hom N

/-- Compact support applied on its specified etale-origin domain to omega_h.
Source: chart proof Step 1 (blueprint: def-pur-general-chart-comparisons). -/
def supportOmega (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e] :=
  letI := Dnc.compactifiable P e (g ≫ aY)
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) e).obj
    (omega P (e ≫ g) aY)

end WeilConjectures.PurityFiniteSetting.ChartComparisons
