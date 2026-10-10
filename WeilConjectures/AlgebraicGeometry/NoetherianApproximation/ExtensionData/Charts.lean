/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.OpensCone
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Cofiltered
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Cone
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The two charts of a stage scheme

Each stage scheme is covered by the chart coming from the Noetherian stage `Dⱼ` and the chart
coming from `Spec A`. This file shows that the cone of stage schemes restricts to limit cones
over the first chart and over the intersection of the two charts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation
namespace ExtensionData

variable (E : ExtensionData.{u})
variable {E}

/-! ### The two charts of a stage scheme -/

/-- (Implementation) The chart of a stage scheme coming from the Noetherian stage `Dⱼ`. -/
noncomputable abbrev Stage.chartU (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inl (E.Wι T.j) T.toSpec).opensRange

/-- (Implementation) The chart of a stage scheme coming from `Spec A`. -/
noncomputable abbrev Stage.chartV (T : E.Stage) : (E.stageDiagram.obj T).Opens :=
  (pushout.inr (E.Wι T.j) T.toSpec).opensRange

lemma Stage.chartU_sup_chartV (T : E.Stage) : T.chartU ⊔ T.chartV = ⊤ :=
  opensRange_pushout_inl_sup_opensRange_pushout_inr _ _

lemma Stage.preimage_chartU {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartU = T.chartU :=
  preimage_opensRange_pushout_inl_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_toSpec f)

lemma Stage.preimage_chartV {T T' : E.Stage} (f : T ⟶ T') :
    E.stageDiagram.map f ⁻¹ᵁ T'.chartV = T.chartV :=
  preimage_opensRange_pushout_inr_of_isPullback _ _ _ _ _ _ _ (WD_map_Wι f.base)
    (Stage.toSpec_comp_SpecMap_algHom f).symm (isPullback_Wι f)

lemma Stage.chartU_inf_chartV (T : E.Stage) :
    T.chartU ⊓ T.chartV = (E.Wι T.j ≫ pushout.inl (E.Wι T.j) T.toSpec).opensRange := by
  rw [Scheme.Hom.opensRange_comp (E.Wι T.j) (pushout.inl (E.Wι T.j) T.toSpec),
    ← preimage_opensRange_pushout_inr (E.Wι T.j) T.toSpec,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

lemma Stage.fromX_preimage_chartU (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartU = E.U := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · exact h
    · -- `x` lies in `V`; its image in `Spec A` lies in the image of `Wⱼ`, hence in one of
      -- the basic opens of the generators, which are contained in `U`.
      obtain ⟨y, hy⟩ : ∃ y, pushout.inl (E.Wι T.j) T.toSpec y = T.fromX x := hx
      set x' : E.V.toScheme := ⟨x, h⟩ with hx'
      have hfV : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
          (Spec.map T.φ (E.V.toSpecΓ x')) :=
        calc T.fromX x = (E.V.ι ≫ T.fromX) x' := rfl
          _ = T.fromV x' := by rw [Stage.Vι_fromX]
          _ = _ := rfl
      rw [hfV] at hy
      obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy
      have hq : Spec.map T.φ (E.V.toSpecΓ x') ∈ T.toSpec.opensRange := ⟨w, hw⟩
      rw [T.opensRange_toSpec] at hq
      obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
      have hl' : E.V.toSpecΓ x' ∈ Spec.map T.φ ⁻¹ᵁ PrimeSpectrum.basicOpen (T.h l) := hl
      rw [SpecMap_preimage_basicOpen] at hl'
      have hb : (T.φ (T.h l) : Γ(E.X, E.V)) = E.b l := rfl
      rw [hb] at hl'
      have : x' ∈ E.V.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (E.b l) := hl'
      rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at this
      exact ((E.hb l) this).1
  · change T.fromX x ∈ T.chartU
    have h1 : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec
        (E.N.π.app T.j.left (⟨x, hx⟩ : E.U.toScheme)) :=
      calc T.fromX x = (E.U.ι ≫ T.fromX) (⟨x, hx⟩ : E.U.toScheme) := rfl
        _ = T.fromU (⟨x, hx⟩ : E.U.toScheme) := by rw [Stage.Uι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartV (T : E.Stage) : T.fromX ⁻¹ᵁ T.chartV = E.V := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hmem : x ∈ E.U ⊔ E.V := by rw [E.hUV]; trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h | h
    · obtain ⟨y, hy⟩ : ∃ y, pushout.inr (E.Wι T.j) T.toSpec y = T.fromX x := hx
      set x' : E.U.toScheme := ⟨x, h⟩ with hx'
      have hfU : T.fromX x = pushout.inl (E.Wι T.j) T.toSpec (E.N.π.app T.j.left x') :=
        calc T.fromX x = (E.U.ι ≫ T.fromX) x' := rfl
          _ = T.fromU x' := by rw [Stage.Uι_fromX]
          _ = _ := rfl
      rw [hfU] at hy
      obtain ⟨w, hw, -⟩ := (pushout_inl_eq_inr_iff (E.Wι T.j) T.toSpec _ _).mp hy.symm
      have hp : E.N.π.app T.j.left x' ∈ (E.Wι T.j).opensRange := ⟨w, hw⟩
      rw [opensRange_Wι] at hp
      have hp' : E.N.π.app E.i₀ x' ∈ E.W₀ := by
        rw [← E.N_π_naturality T.j.hom, Scheme.Hom.comp_apply]
        exact hp
      have : x' ∈ E.N.π.app E.i₀ ⁻¹ᵁ E.W₀ := hp'
      rw [E.hW₀] at this
      exact this
    · exact h
  · change T.fromX x ∈ T.chartV
    have h1 : T.fromX x = pushout.inr (E.Wι T.j) T.toSpec
        (Spec.map T.φ (E.V.toSpecΓ (⟨x, hx⟩ : E.V.toScheme))) :=
      calc T.fromX x = (E.V.ι ≫ T.fromX) (⟨x, hx⟩ : E.V.toScheme) := rfl
        _ = T.fromV (⟨x, hx⟩ : E.V.toScheme) := by rw [Stage.Vι_fromX]
        _ = _ := rfl
    rw [h1]
    exact ⟨_, rfl⟩

lemma Stage.fromX_preimage_chartU_inf_chartV (T : E.Stage) :
    T.fromX ⁻¹ᵁ (T.chartU ⊓ T.chartV) = E.U ⊓ E.V := by
  rw [Scheme.Hom.preimage_inf, T.fromX_preimage_chartU, T.fromX_preimage_chartV]

/-! ### The limit property, chart by chart -/

/-- (Implementation) The system of Noetherian stages `Dⱼ`, indexed by the stages below a
fixed stage. -/
noncomputable abbrev baseDiagram (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀ ⋙ E.N.D

/-- (Implementation) `U` is the limit of the Noetherian stages `Dⱼ` indexed by the stages
below a fixed stage: the index functor is initial. -/
noncomputable def isLimitBaseCone (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.cone).symm E.N.isLimit

/-- (Implementation) The `U`-chart of a stage scheme is `Dⱼ`, compatibly with the
transition morphisms. -/
noncomputable def chartUIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    E.baseDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ T₀.chartU :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))
      ((Scheme.Hom.coe_opensRange _).symm.trans
        ((congrArg SetLike.coe (Stage.preimage_chartU S.hom).symm).trans
          (Scheme.Opens.range_ι _).symm)))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map]
      rfl)

set_option maxHeartbeats 1600000 in
-- Transporting the limit along the chart isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the `U`-chart is a limit cone. -/
noncomputable def isLimitOpensConeChartU (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU) :=
  IsLimit.equivOfNatIsoOfIso (E.chartUIso T₀)
    (E.cone.whisker (Over.forget T₀ ⋙ E.stageIndex ⋙ Over.forget E.i₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartU)
    (Cone.ext (E.X.isoOfEq T₀.fromX_preimage_chartU.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartU))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Category.assoc, chartUIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Scheme.isoOfEq_hom_ι_assoc]
      exact (Stage.Uι_fromX S.left).symm))
    (E.isLimitBaseCone T₀)

/-- (Implementation) The system of intersections `Wⱼ`, indexed by the stages below a fixed
stage. -/
noncomputable abbrev interDiagram (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over T₀ ⥤ Scheme.{u} :=
  Over.forget T₀ ⋙ E.stageIndex ⋙ E.WD

/-- (Implementation) `W = U ⊓ V` is the limit of the `Wⱼ` indexed by the stages below a
fixed stage. -/
noncomputable def isLimitInterCone (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ E.Wc).symm E.isLimitWc

/-- (Implementation) The overlap of the two charts of a stage scheme is `Wⱼ`, compatibly
with the transition morphisms. -/
noncomputable def interIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    E.interDiagram T₀ ≅ opensDiagram E.stageDiagram T₀ (T₀.chartU ⊓ T₀.chartV) :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq
      (E.Wι S.left.j ≫ pushout.inl (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ (T₀.chartU ⊓ T₀.chartV)))
      ((Scheme.Hom.coe_opensRange _).symm.trans
        ((congrArg SetLike.coe ((congrArg₂ (· ⊓ ·) (Stage.preimage_chartU S.hom)
          (Stage.preimage_chartV S.hom)).trans (Stage.chartU_inf_chartV _)).symm).trans
            (Scheme.Opens.range_ι _).symm)))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      have h : (E.interDiagram T₀).map k = E.WD.map k.left.base := rfl
      simp only [h, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inl_stageDiagram_map,
        WD_map_Wι_assoc])

set_option maxHeartbeats 1600000 in
-- Transporting the limit along the overlap isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the overlap of the two charts is a
limit cone. -/
noncomputable def isLimitOpensConeInter (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV)) :=
  IsLimit.equivOfNatIsoOfIso (E.interIso T₀)
    (E.Wc.whisker (Over.forget T₀ ⋙ E.stageIndex))
    (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartV))
    (Cone.ext (E.θ.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartU_inf_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ
        (T₀.chartU ⊓ T₀.chartV)))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, interIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, θ_inv_infι_assoc, stageCone_π_app]
      exact (E.Wc_π_Wι_assoc S.left.j _).trans (by rw [Stage.Uι_fromX, Stage.fromU])))
    (E.isLimitInterCone T₀)

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
