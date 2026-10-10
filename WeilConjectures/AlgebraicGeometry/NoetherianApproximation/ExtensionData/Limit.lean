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
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Charts
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
# The extended system is a Noetherian approximation

The sections of `V` are the filtered colimit of the coefficient algebras of the stages, so the
cone of stage schemes restricts to a limit cone over the `Spec A`-chart as well. Hence it is a
limit cone, and the stages form a Noetherian approximation of `X`
(`ExtensionData.approximation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation
namespace ExtensionData

variable (E : ExtensionData.{u})
variable {E}

/-! ### The `Spec A`-chart: the sections of `V` are the colimit of the coefficient algebras -/

/-- (Implementation) Every section of `V` occurs in the coefficient algebra of some stage. -/
lemma exists_stage_mem_A (E : ExtensionData.{u}) (β : Γ(E.X, E.V)) :
    ∃ (T : E.Stage) (a : ↥T.A), (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 = β := by
  obtain ⟨T₁⟩ := (inferInstance : Nonempty E.Stage)
  obtain ⟨j₁, x₁, hx₁⟩ := exists_appTop_π_eq_of_isLimit E.WD E.Wc E.isLimitWc (E.sV β)
  obtain ⟨j₂, k₁, k₂, -⟩ := IsCofilteredOrEmpty.cone_objs T₁.j j₁
  have hxt : E.t j₂ (E.res k₂ x₁) = E.sV β := by rw [E.t_res]; exact hx₁.symm
  have hle : Algebra.adjoin ℤ {(β, E.res k₂ x₁)} ≤ E.fiberProduct j₂ :=
    Algebra.adjoin_le (by rintro p rfl; exact (E.mem_fiberProduct_iff _).mpr hxt.symm)
  have hfg : (Algebra.adjoin ℤ {(β, E.res k₂ x₁)}).FG :=
    Subalgebra.fg_def.mpr ⟨_, Set.finite_singleton _, rfl⟩
  exact ⟨T₁.restrict k₁ _ hle hfg,
    ⟨(β, E.res k₂ x₁), T₁.le_restrict_A k₁ _ hle hfg (Algebra.subset_adjoin rfl)⟩, rfl⟩

/-- (Implementation) Two elements of a coefficient algebra whose components agree are
equal. -/
lemma Stage.Hom.algHom_eq_of {T T' : E.Stage} (f : T' ⟶ T) (a b : ↥T.A)
    (h1 : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1)
    (h2 : E.res f.base (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.res f.base (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2) :
    f.algHom a = f.algHom b :=
  Subtype.ext (by rw [Stage.Hom.algHom_coe, Stage.Hom.algHom_coe, h1, h2])

/-- (Implementation) Two elements of a coefficient algebra with the same `V`-component become
equal at a later stage: their `Wⱼ`-components agree on the intersection `W`, hence already at
a finite stage. -/
lemma exists_hom_algHom_eq (E : ExtensionData.{u}) (T : E.Stage) (a b : ↥T.A)
    (h : (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1 =
      (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).1) :
    ∃ (T' : E.Stage) (f : T' ⟶ T), f.algHom a = f.algHom b := by
  have ht : E.t T.j (a : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 =
      E.t T.j (b : Γ(E.X, E.V) × Γ(E.WD.obj T.j, ⊤)).2 := by
    rw [← T.hA _ a.2, ← T.hA _ b.2, h]
  have hcpt : IsCompact ((⊤ : (E.WD.obj T.j).Opens) : Set (E.WD.obj T.j)) := isCompact_univ
  obtain ⟨j', k, hk⟩ := exists_app_map_eq_map_of_isLimit E.WD E.Wc E.isLimitWc hcpt _ _ ht
  -- Stated for a general subalgebra `A'`: at `A' = ⊥`, unifying `hk` with the goal is very
  -- slow.
  have H (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤))) (hA' : A' ≤ E.fiberProduct j')
      (hfg : A'.FG) : ∃ (T' : E.Stage) (f : T' ⟶ T), f.algHom a = f.algHom b :=
    ⟨T.restrict k A' hA' hfg, T.restrictHom k A' hA' hfg, Stage.Hom.algHom_eq_of _ a b h hk⟩
  exact H ⊥ bot_le Subalgebra.fg_bot

/-- (Implementation) The system of coefficient algebras of the stages, as a diagram in the
opposite category of commutative rings. -/
noncomputable def algOp (E : ExtensionData.{u}) : E.Stage ⥤ CommRingCatᵒᵖ where
  obj T := Opposite.op (CommRingCat.of ↥T.A)
  map f := (f.algHom).op
  map_id T := Quiver.Hom.unop_inj (Stage.Hom.algHom_id T)
  map_comp f g := Quiver.Hom.unop_inj (Stage.Hom.algHom_comp f g)

/-- (Implementation) `Γ(X, V)` as a cocone on the system of coefficient algebras. -/
noncomputable def algCocone (E : ExtensionData.{u}) : Cocone E.algOp.leftOp where
  pt := Γ(E.X, E.V)
  ι :=
    { app := fun T ↦ T.unop.φ
      naturality := fun _ _ f ↦
        (Stage.Hom.algHom_φ f.unop).trans (Category.comp_id _).symm }

set_option maxHeartbeats 1600000 in
-- Reflecting the colimit through the forgetful functor unfolds the subalgebra
-- coercions of every stage.
/-- (Implementation) `Γ(X, V)` is the filtered colimit of the coefficient algebras of the
stages: every section of `V` occurs at some stage, and two elements with the same
`V`-component become equal at a later stage. -/
noncomputable def isColimitAlgCocone (E : ExtensionData.{u}) : IsColimit E.algCocone := by
  have : ReflectsColimit E.algOp.leftOp (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun β ↦ ?_) (fun T a b hab ↦ ?_)
  · obtain ⟨T, a, ha⟩ := E.exists_stage_mem_A β
    exact ⟨Opposite.op T, a, ha.symm⟩
  · obtain ⟨T', f, hf⟩ := E.exists_hom_algHom_eq T.unop a b hab
    exact ⟨Opposite.op T', f.op, hf⟩

/-- (Implementation) The system of the spectra of the coefficient algebras. -/
noncomputable abbrev specDiagram (E : ExtensionData.{u}) : E.Stage ⥤ Scheme.{u} :=
  E.algOp ⋙ Scheme.Spec

/-- (Implementation) `V ≅ Spec Γ(X, V)` as a cone on the spectra of the coefficient
algebras. -/
noncomputable def specCone (E : ExtensionData.{u}) : Cone E.specDiagram :=
  Scheme.Spec.mapCone (Limits.coneOfCoconeLeftOp E.algCocone)

lemma specCone_pt (E : ExtensionData.{u}) : E.specCone.pt = Spec Γ(E.X, E.V) := rfl

lemma specCone_π_app (E : ExtensionData.{u}) (T : E.Stage) :
    E.specCone.π.app T = Spec.map T.φ := rfl

/-- (Implementation) `Spec Γ(X, V)` is the limit of the spectra of the coefficient
algebras. -/
noncomputable def isLimitSpecCone (E : ExtensionData.{u}) : IsLimit E.specCone :=
  isLimitOfPreserves Scheme.Spec
    (Limits.isLimitConeOfCoconeLeftOp E.algOp E.isColimitAlgCocone)

@[reassoc (attr := simp)]
lemma isoSpec_inv_toSpecΓ (E : ExtensionData.{u}) :
    E.hV.isoSpec.inv ≫ E.V.toSpecΓ = 𝟙 _ := by
  rw [← IsAffineOpen.isoSpec_hom E.hV, Iso.inv_hom_id]

/-- (Implementation) The `Spec A`-chart of a stage scheme is `Spec A`, compatibly with the
transition morphisms. -/
noncomputable def chartVIso (E : ExtensionData.{u}) (T₀ : E.Stage) :
    Over.forget T₀ ⋙ E.specDiagram ≅ opensDiagram E.stageDiagram T₀ T₀.chartV :=
  NatIso.ofComponents
    (fun S ↦ IsOpenImmersion.isoOfRangeEq (pushout.inr (E.Wι S.left.j) S.left.toSpec)
      (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))
      ((Scheme.Hom.coe_opensRange _).symm.trans
        ((congrArg SetLike.coe (Stage.preimage_chartV S.hom).symm).trans
          (Scheme.Opens.range_ι _).symm)))
    (fun {S S'} k ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S'.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        opensDiagram_map_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, inr_stageDiagram_map]
      rfl)

set_option maxHeartbeats 1600000 in
-- Transporting the limit along the chart isomorphism compares two cones on the
-- opens diagram of the pushout.
/-- (Implementation) The restriction of the stage cone to the `Spec A`-chart is a limit
cone. -/
noncomputable def isLimitOpensConeChartV (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV) :=
  IsLimit.equivOfNatIsoOfIso (E.chartVIso T₀)
    (E.specCone.whisker (Over.forget T₀))
    (opensCone E.stageDiagram E.stageCone T₀ T₀.chartV)
    (Cone.ext (E.hV.isoSpec.symm ≪≫ E.X.isoOfEq T₀.fromX_preimage_chartV.symm) (fun S ↦ by
      rw [← cancel_mono (Scheme.Opens.ι (E.stageDiagram.map S.hom ⁻¹ᵁ T₀.chartV))]
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Cone.whisker_π,
        Functor.whiskerLeft_app, Category.assoc, chartVIso, NatIso.ofComponents_hom_app,
        IsOpenImmersion.isoOfRangeEq_hom_fac, opensCone_π_ι, Iso.trans_hom,
        Scheme.isoOfEq_hom_ι_assoc, Iso.symm_hom, stageCone_π_app]
      rw [Stage.Vι_fromX, Stage.fromV, isoSpec_inv_toSpecΓ_assoc]
      exact congrArg (fun g ↦ g ≫ pushout.inr (E.Wι S.left.j) S.left.toSpec)
        (specCone_π_app E S.left)))
    ((Functor.Initial.isLimitWhiskerEquiv _ E.specCone).symm E.isLimitSpecCone)

/-- (Implementation) The two charts of a stage scheme, as a family indexed by `Bool`. -/
noncomputable def charts (E : ExtensionData.{u}) (T₀ : E.Stage) (b : Bool) :
    (E.stageDiagram.obj T₀).Opens :=
  bif b then T₀.chartU else T₀.chartV

set_option maxHeartbeats 1600000 in
-- Each of the four cases unfolds the pushout defining the stage scheme.
/-- (Implementation) The stage cone is a limit cone: its restrictions to the two charts of a
stage scheme and to their overlap are limit cones. -/
noncomputable def isLimitStageConeOfStage (E : ExtensionData.{u}) (T₀ : E.Stage) :
    IsLimit E.stageCone := by
  refine isLimitOfIsLimitOpensCone E.stageDiagram E.stageCone T₀ (E.charts T₀) ?_
    (fun b ↦ ?_) (fun b b' ↦ ?_)
  · rw [iSup_bool_eq]
    exact T₀.chartU_sup_chartV
  · cases b
    exacts [E.isLimitOpensConeChartV T₀, E.isLimitOpensConeChartU T₀]
  · cases b <;> cases b'
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartV ⊓ T₀.chartV))
      rw [inf_idem]
      exact E.isLimitOpensConeChartV T₀
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartV ⊓ T₀.chartU))
      rw [inf_comm]
      exact E.isLimitOpensConeInter T₀
    · exact E.isLimitOpensConeInter T₀
    · change IsLimit (opensCone E.stageDiagram E.stageCone T₀ (T₀.chartU ⊓ T₀.chartU))
      rw [inf_idem]
      exact E.isLimitOpensConeChartU T₀

/-- (Implementation) The stage cone is a limit cone. -/
noncomputable def isLimitStageCone (E : ExtensionData.{u}) : IsLimit E.stageCone :=
  E.isLimitStageConeOfStage (Classical.arbitrary E.Stage)

/-- (Implementation) The Noetherian approximation of `X = U ∪ V` extending a given
approximation of `U` across the affine open `V`. This is the induction step of
Stacks Project Tag 07RN. -/
noncomputable def approximation (E : ExtensionData.{u}) : E.X.NoetherianApproximation where
  I := E.Stage
  D := E.stageDiagram
  locallyOfFiniteType_obj _ := inferInstance
  compactSpace_obj _ := inferInstance
  isAffineHom_map _ := inferInstance
  π := E.stageCone.π
  isLimit := E.isLimitStageCone

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
