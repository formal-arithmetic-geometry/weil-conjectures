/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates

/-!
# Open restriction as ordinary pullback

For an open immersion `j`, the restriction of completed-ring modules to the open pro-etale
site is identified with the ordinary module pullback along `j`.

## Main definitions

- `AlgebraicGeometry.Scheme.cbcRestrictionUnit`: restriction of sections, as the unit from a
  module to the direct image of its open restriction.
- `AlgebraicGeometry.Scheme.cbcPullToRestriction`: the comparison from ordinary pullback to
  open restriction, transposed from that unit.

## Main statements

- `AlgebraicGeometry.Scheme.cbcPullToRestriction_isIso`: the comparison is invertible.

## References

* Stacks Project, Tags 03DI and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The projection of an open pullback, as an arrow in the original pro-etale site. -/
def cbcOpenProjection {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (V : T.ProEt) :
    (cbcOpenSiteFunctor j inferInstance).obj ((proEtaleBaseChange j).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom j) pullback.condition

/-- The coefficient counit equation follows from the constant-sheafification unit. -/
private theorem cbcFiniteCoefficientCounit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :
    let F := proEtaleBaseChange j
    let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let R := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) T
    let S := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) U
    let ψ := proEtaleRingDirectImageMap j R S
      (ProEtale.StrictTower.constantRingIso (cbcFiniteRing d n) j)
    Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft (finiteOpenRing d j inferInstance n).hom.hom := by
  dsimp only
  let F := proEtaleBaseChange j
  let G := cbcOpenSiteFunctor j inferInstance
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let R := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) T
  let S := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) U
  let ψ := proEtaleRingDirectImageMap j R S
    (ProEtale.StrictTower.constantRingIso (cbcFiniteRing d n) j)
  have hψ : ψ = proEtaleConstantDirectImageMap j CommRingCat.{t + 1}
      (cbcFiniteRing d n) := by
    change (proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  change Functor.whiskerRight (NatTrans.op a.counit) R.obj =
    ψ.hom ≫ F.op.whiskerLeft (finiteOpenRing d j inferInstance n).hom.hom
  apply sheafify_hom_ext (ProEt.topology T) _ _
    (((proEtaleSheafDirectImage j CommRingCat.{t + 1}).obj
      ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R)).property)
  rw [hψ]
  have hunit : toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n)) ≫
      (proEtaleConstantDirectImageMap j CommRingCat.{t + 1}
        (cbcFiniteRing d n)).hom =
      F.op.whiskerLeft (toSheafify (ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (cbcFiniteRing d n))) := by
    exact (sheafificationAdjunction (ProEt.topology T) CommRingCat.{t + 1}).homEquiv
      _ _ |>.apply_symm_apply _
  rw [← Category.assoc]
  erw [hunit]
  ext V b
  have hc := ConcreteCategory.congr_hom
    (congr_app (finiteOpenRing_unit d j inferInstance n) (F.op.obj V)) b
  have hn := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).naturality
        (a.counit.app V.unop).op) b
  exact hn.symm.trans hc.symm

/-- Completed scalar compatibility is detected by the finite limit projections. -/
theorem cbcCompletedCoefficientCounit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    let F := proEtaleBaseChange j
    let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let ψ := proEtaleRingDirectImageMap j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)
    Functor.whiskerRight (NatTrans.op a.counit) (d.completedRing T).obj =
      ψ.hom ≫ F.op.whiskerLeft (cbcCompletedRestrictionMap d j inferInstance).hom := by
  let F := proEtaleBaseChange j
  let G := cbcOpenSiteFunctor j inferInstance
  let E := sheafToPresheaf (ProEt.topology T) CommRingCat.{t + 1} ⋙
    (Functor.whiskeringLeft T.ProEtᵒᵖ T.ProEtᵒᵖ CommRingCat.{t + 1}).obj (F ⋙ G).op
  apply (isLimitOfPreserves E (limit.isLimit (reductionCoefficientSystem T d))).hom_ext
  intro n
  dsimp only [Functor.mapCone_π_app, Functor.comp_map]
  apply (cancel_mono (E.map (pbcLevelConstantComparison T d n.unop).inv)).1
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let π := cbcFiniteProjection d T n.unop
  let π' := cbcFiniteProjection d U n.unop
  let ψ := cbcCompletedCoefficientDirectMap d j
  let ψ' := proEtaleRingDirectImageMap j
    (ProEtale.StrictTower.coefficients (cbcFiniteRing d n.unop) T)
    (ProEtale.StrictTower.coefficients (cbcFiniteRing d n.unop) U)
    (ProEtale.StrictTower.constantRingIso (cbcFiniteRing d n.unop) j)
  have hψ : proEtaleRingDirectImageMap j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j) = ψ := by
    dsimp [ψ, cbcCompletedCoefficientDirectMap, proEtaleRingDirectImageMap]
    rw [cbcDatumCoefficient_eq d j]
    rfl
  have hπ : ψ.hom ≫ F.op.whiskerLeft π'.hom = π.hom ≫ ψ'.hom := by
    exact congrArg (fun z ↦ z.hom) (finiteProjection_direct d j n.unop).symm
  have hres : (cbcCompletedRestrictionMap d j inferInstance).hom ≫
      G.op.whiskerLeft π.hom = π'.hom ≫ (finiteOpenRing d j inferInstance n.unop).hom.hom := by
    exact congrArg (fun z ↦ z.hom) (finiteOpenRing_projection d j inferInstance n.unop).symm
  change Functor.whiskerRight (NatTrans.op a.counit) (d.completedRing T).obj ≫
      (F ⋙ G).op.whiskerLeft π.hom =
    (proEtaleRingDirectImageMap j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).hom ≫
      F.op.whiskerLeft (cbcCompletedRestrictionMap d j inferInstance).hom ≫
        (F ⋙ G).op.whiskerLeft π.hom
  rw [hψ]
  have hn : Functor.whiskerRight (NatTrans.op a.counit) (d.completedRing T).obj ≫
      (F ⋙ G).op.whiskerLeft π.hom =
    π.hom ≫ Functor.whiskerRight (NatTrans.op a.counit)
      (ProEtale.StrictTower.coefficients (cbcFiniteRing d n.unop) T).obj := by
    apply NatTrans.ext
    funext V
    exact π.hom.naturality (a.counit.app V.unop).op
  rw [hn, cbcFiniteCoefficientCounit d j n.unop]
  calc
    _ = (π.hom ≫ ψ'.hom) ≫
        F.op.whiskerLeft (finiteOpenRing d j inferInstance n.unop).hom.hom := by
      rfl
    _ = (ψ.hom ≫ F.op.whiskerLeft π'.hom) ≫
        F.op.whiskerLeft (finiteOpenRing d j inferInstance n.unop).hom.hom := by rw [hπ]
    _ = ψ.hom ≫ F.op.whiskerLeft
        (π'.hom ≫ (finiteOpenRing d j inferInstance n.unop).hom.hom) := by
      rfl
    _ = _ := by rw [← hres]; rfl

/-- Lift the open-site adjunction using the normalized coefficient counit equation. -/
private def cbcRestrictionAdjunction {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    cbcOpenRestriction d j inferInstance ⊣
      proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) := by
  let F := proEtaleBaseChange j
  let G := cbcOpenSiteFunctor j inferInstance
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let R := d.completedRing T
  let S := d.completedRing U
  let c := cbcCompletedRestrictionMap d j inferInstance
  let ψ := proEtaleRingDirectImageMap j R S (d.integralRingIso j)
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft c.hom := cbcCompletedCoefficientCounit d j
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{t + 1})
    (ProEt.topology U) (ProEt.topology T)
  let e := ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).app R
  have hc : (d.integralRingIso j).hom ≫ c = e.hom := by
    apply ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _).injective
    change ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
      ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R)) ((d.integralRingIso j).hom ≫ c) =
      ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
        ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R))
        (((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).hom.app R)
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    apply Sheaf.hom_ext
    change ψ.hom ≫ F.op.whiskerLeft c.hom =
      Functor.whiskerRight (NatTrans.op a.counit) R.obj
    exact H₁.symm
  have heq : c = ((d.integralRingIso j).symm ≪≫ e).hom := by
    apply (cancel_epi (d.integralRingIso j).hom).1
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc] using hc
  have : IsIso c := by rw [heq]; infer_instance
  have H₂ : c.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.app V)).1
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun z ↦ z.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.app (F.op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = c.hom.app V
    rw [R.obj.map_id]
    exact Category.comp_id _
  let Rr := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let φr : Sr ⟶ (G.sheafPushforwardContinuous RingCat.{t + 1}
      (ProEt.topology U) (ProEt.topology T)).obj Rr :=
    (sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map c
  let ψr : Rr ⟶ (F.sheafPushforwardContinuous RingCat.{t + 1}
      (ProEt.topology T) (ProEt.topology U)).obj Sr :=
    ⟨Functor.whiskerRight ψ.hom (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩
  have H₁r : Functor.whiskerRight (NatTrans.op a.counit) Rr.obj =
      ψr.hom ≫ F.op.whiskerLeft φr.hom := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}).map
      (z.app V)) H₁
  have H₂r : φr.hom ≫ G.op.whiskerLeft ψr.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) Sr.obj = 𝟙 Sr.obj := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}).map
      (z.app V)) H₂
  exact SheafOfModules.pushforwardPushforwardAdj a φr ψr H₁r H₂r

private theorem cbcRestrictionAdjunction_unit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (M : proEtaleRingModules T (d.completedRing T)) (V : T.ProEt)
    (x : M.val.obj (op V)) :
    ((cbcRestrictionAdjunction d j).unit.app M).val.app (op V) x =
      M.val.map (cbcOpenProjection j V).op x := by
  unfold cbcRestrictionAdjunction
  rfl

/-- Restriction of sections is the unit from a module to direct image of open restriction.
Its section formula fixes the comparison, including its completed scalar action. -/
theorem cbcRestrictionUnit_existsUnique {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    ∃! η : 𝟭 (proEtaleRingModules T (d.completedRing T)) ⟶
        cbcOpenRestriction d j inferInstance ⋙
          proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
            (d.integralRingIso j),
      ∀ (M : proEtaleRingModules T (d.completedRing T)) (V : T.ProEt)
        (x : M.val.obj (op V)),
        (η.app M).val.app (op V) x = M.val.map (cbcOpenProjection j V).op x := by
  refine ⟨(cbcRestrictionAdjunction d j).unit,
    cbcRestrictionAdjunction_unit d j, ?_⟩
  intro θ hθ
  ext M V x
  exact (hθ M V.unop x).trans (cbcRestrictionAdjunction_unit d j M V.unop x).symm

/-- The section-normalized restriction unit. -/
def cbcRestrictionUnit {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRestrictionUnit_existsUnique d j).choose

-- Transposing the section unit compares the concrete and small-model module categories.
/-- Ordinary inverse image identifies with open restriction by transposing its section unit. -/
def cbcPullToRestriction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) ⟶ cbcOpenRestriction d j inferInstance :=
  (((proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)).whiskerRight
      (proEtaleRingModules T (d.completedRing T))).homEquiv
        (𝟭 (proEtaleRingModules T (d.completedRing T)))
          (cbcOpenRestriction d j inferInstance)).symm (cbcRestrictionUnit d j)

/-- The specified restriction comparison is invertible. -/
theorem cbcPullToRestriction_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcPullToRestriction d j) := by
  let a := proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)
  let b := cbcRestrictionAdjunction d j
  have hu : cbcRestrictionUnit d j = b.unit := by
    apply (cbcRestrictionUnit_existsUnique d j).unique
    · exact (cbcRestrictionUnit_existsUnique d j).choose_spec.1
    · exact cbcRestrictionAdjunction_unit d j
  have he : cbcPullToRestriction d j = (a.leftAdjointUniq b).hom := by
    apply (a.whiskerRight (proEtaleRingModules T (d.completedRing T))).homEquiv
      (𝟭 _) (cbcOpenRestriction d j inferInstance) |>.injective
    rw [cbcPullToRestriction, Equiv.apply_symm_apply, hu]
    apply NatTrans.ext
    funext M
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b M).symm
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
