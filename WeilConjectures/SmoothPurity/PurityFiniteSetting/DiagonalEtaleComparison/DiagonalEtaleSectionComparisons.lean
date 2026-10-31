/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraFlatBaseChange
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.ChartNormalDifferential.ChartNormalDifferential

/-! # Orientation-free section and normal comparisons

These constructions reuse the explicit self-product, Rees and zero-fibre argument of
GeneralChartComparisons without importing its downstream diagonal-orientation theorem.
Only the counit and geometric exchanges occur; no orientation is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison

/-- The map e times e on self-products. Source: chart proof Step 1
(blueprint: def-pur-diagonal-etale-section-comparisons). -/
def selfMap {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  pullback.map h h g
    g e e (𝟙 Y)
    ((Category.comp_id h).trans w.symm) ((Category.comp_id h).trans w.symm)

/-- The first projection of e times e is e after the first projection.
Source: chart proof Step 1 (blueprint: def-pur-diagonal-etale-section-comparisons).
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

/-- The diagonal ideal pulls into the diagonal ideal under e times e.
Source: chart proof Steps 1--2 (blueprint: def-pur-diagonal-etale-section-comparisons).
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
Source: chart proof Step 3 (blueprint: def-pur-diagonal-etale-section-comparisons). -/
def deformation {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y) [IsSeparated h]
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  Scheme.IdealSheafData.deformationSpaceMap (selfMap d g h e w)
    (pullback.diagonal g).ker
    (pullback.diagonal h).ker (fun {_ _} H ↦ idealCondition d g h e w H)

/-- The Rees comparison restricts to the actual zero fibre over e.
Source: chart proof Step 3 (blueprint: def-pur-diagonal-etale-section-comparisons).
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
Source: chart proof Steps 2--3 (blueprint: def-pur-diagonal-etale-section-comparisons). -/
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
(blueprint: def-pur-diagonal-etale-section-comparisons).
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
Source: chart proof Steps 3--4 (blueprint: def-pur-diagonal-etale-section-comparisons). -/
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

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
