module
public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
import Sheaf.AlgebraicGeometry.AffineResidueScalarTransport
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
set_option maxHeartbeats 1000000 in
-- Comparing the explicit tensor quotient with categorical kernels needs extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit residue quotient comparison can be chosen naturally in every chain map.
Source: Stacks Project, Tag 010V. Use the same residue scalar transport on every term;
it commutes with module maps. The kernel and quotient comparisons then commute with
cycles and homology maps by their universal properties.
(blueprint: new-picard-residue-quotient-model-homology) -/
theorem picard_residue_quotient_model_homology_naturality
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let G := (F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)
    ∃ e : ∀ K : CochainComplex
        (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ,
      affineResidueCycleHomology W U p K ≃+ (G.obj K).homology 1,
      ∀ (K C : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
        (φ : K ⟶ C) (z : affineResidueCycleHomology W U p K),
        e C (affineResidueCycleHomologyMap φ z) =
          HomologicalComplex.homologyMap (G.map φ) 1 (e K z) := by
  classical
  dsimp only
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  let : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  let : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let G := (F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)
  have hp' : p = (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal := by
    rw [hp, hU.isoSpec_hom_apply]
    ext a
    change W.evaluation U w hwU a = 0 ↔
      W.presheaf.germ U w hwU a ∈ IsLocalRing.maximalIdeal _
    exact IsLocalRing.residue_eq_zero_iff _
  clear hp
  subst p
  obtain ⟨δ⟩ := affine_residue_scalar_transport W U hU ⟨w, hwU⟩
  let κ := (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.ResidueField
  let a : κ ≃ₗ[Γ(W, U)]
      (ModuleCat.restrictScalars (algebraMap Γ(W, U) κ)).obj (ModuleCat.of κ κ) :=
    { AddEquiv.refl κ with
      map_smul' := fun r x ↦ Algebra.smul_def r x }
  let t (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (j : ℤ) :=
    TensorProduct.congr a (LinearEquiv.refl Γ(W, U) (F.obj (K.X j)))
  let e (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (j : ℤ) :
      affineResidueTerm W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K j ≃+
        (G.obj K).X j :=
    (t K j).toAddEquiv.trans (δ.app (F.obj (K.X j))).toLinearEquiv.toAddEquiv
  have he (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
      (i j : ℤ) (x : affineResidueTerm W U
        (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K i) :
      e K j (affineResidueDifferential W U _ K i j x) =
        (G.obj K).d i j (e K i x) := by
    let S := ModuleCat.extendScalars.{v, v, v} (algebraMap Γ(W, U) κ)
    have ht : t K j (affineResidueDifferential W U _ K i j x) =
        S.map (F.map (K.d i j)) (t K i x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r m => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    change (δ.hom.app (F.obj (K.X j)))
        (t K j (affineResidueDifferential W U _ K i j x)) = _
    rw [ht]
    exact ConcreteCategory.congr_hom (δ.hom.naturality (F.map (K.d i j))) (t K i x)
  let ec (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
      affineResidueCycles W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K ≃+
        LinearMap.ker ((G.obj K).sc' 0 1 2).g.hom :=
    { toFun := fun x ↦ ⟨e K 1 x.val, by
        change (G.obj K).d 1 2 (e K 1 x.val) = 0
        rw [← he, x.property, map_zero]⟩
      invFun := fun x ↦ ⟨(e K 1).symm x.val, by
        apply (e K 2).injective
        rw [he, (e K 1).apply_symm_apply, map_zero]
        exact x.property⟩
      left_inv := fun x ↦ Subtype.ext ((e K 1).symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext ((e K 1).apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext ((e K 1).map_add x.val y.val) }
  let cyc (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
      (x : affineResidueCycles W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K) :
      (G.obj K).cycles 1 :=
    ((G.obj K).cyclesIsoSc' 0 1 2 (by simp) (by simp)).inv
      (((G.obj K).sc' 0 1 2).moduleCatCyclesIso.inv (ec K x))
  have hcyc (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
      (x : affineResidueCycles W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K) :
      (G.obj K).iCycles 1 (cyc K x) = e K 1 x.val := by
    have h₁ := ConcreteCategory.congr_hom
      ((G.obj K).cyclesIsoSc'_inv_iCycles 0 1 2 (by simp) (by simp))
      (((G.obj K).sc' 0 1 2).moduleCatCyclesIso.inv (ec K x))
    have h₂ := ConcreteCategory.congr_hom
      ((G.obj K).sc' 0 1 2).moduleCatCyclesIso_inv_iCycles (ec K x)
    exact h₁.trans h₂
  have hc (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
      ∃ h : affineResidueCycleHomology W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K ≃+
          (G.obj K).homology 1,
        ∀ x : affineResidueCycles W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K,
          h (affineResidueCycleClass W U _ K x) =
            (G.obj K).homologyπ 1 (cyc K x) := by
    let C := G.obj K
    let S := C.sc' 0 1 2
    have hb : (affineResidueBoundaries W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K).map
        (ec K).toAddMonoidHom = S.moduleCatToCycles.range.toAddSubgroup := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz⟩ := hy
        refine ⟨e K 0 z, ?_⟩
        apply Subtype.ext
        change C.d 0 1 (e K 0 z) = e K 1 y.val
        rw [← he, hz]
        rfl
      · rintro ⟨y, hy⟩
        refine ⟨(ec K).symm x, ?_, (ec K).apply_symm_apply x⟩
        refine ⟨(e K 0).symm y, ?_⟩
        change affineResidueDifferential W U _ K 0 1 ((e K 0).symm y) =
          (e K 1).symm x.val
        apply (e K 1).injective
        rw [he, (e K 1).apply_symm_apply, (e K 0).apply_symm_apply]
        exact congrArg Subtype.val hy
    let q := QuotientAddGroup.congr
      (affineResidueBoundaries W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K)
      S.moduleCatToCycles.range.toAddSubgroup (ec K) hb
    let h := q.trans ((S.moduleCatHomologyIso.symm ≪≫
      (C.homologyIsoSc' 0 1 2 (by simp) (by simp)).symm).toLinearEquiv.toAddEquiv)
    refine ⟨h, ?_⟩
    intro x
    have h₁ := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π (ec K x)
    have h₂ := ConcreteCategory.congr_hom
      (C.π_homologyIsoSc'_inv 0 1 2 (by simp) (by simp))
      (S.moduleCatCyclesIso.inv (ec K x))
    exact (congrArg (fun y ↦ (C.homologyIsoSc' 0 1 2 (by simp) (by simp)).inv y)
      h₁.symm).trans h₂
  choose h hh using hc
  refine ⟨h, ?_⟩
  intro K C φ z
  obtain ⟨x, rfl⟩ := (affineResidueCycleClass_surjective_kernel W U _ K).1 z
  rw [affineResidueCycleHomologyMap_class, hh, hh]
  have hterm (j : ℤ) (y : affineResidueTerm W U
      (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K j) :
      e C j (affineResidueComponent φ j y) = (G.map φ).f j (e K j y) := by
    let S := ModuleCat.extendScalars.{v, v, v} (algebraMap Γ(W, U) κ)
    have ht : t C j (affineResidueComponent φ j y) =
        S.map (F.map (φ.f j)) (t K j y) := by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r m => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    change (δ.hom.app (F.obj (C.X j)))
        (t C j (affineResidueComponent φ j y)) = _
    rw [ht]
    exact ConcreteCategory.congr_hom (δ.hom.naturality (F.map (φ.f j))) (t K j y)
  have hcycle : cyc C (affineResidueCycleMap φ x) =
      HomologicalComplex.cyclesMap (G.map φ) 1 (cyc K x) := by
    apply (ModuleCat.mono_iff_injective ((G.obj C).iCycles 1)).1 inferInstance
    have hright := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (G.map φ) 1) (cyc K x)
    change (G.obj C).iCycles 1 _ = (G.obj C).iCycles 1 _
    exact (hcyc C (affineResidueCycleMap φ x)).trans
      ((hterm 1 x.val).trans
        ((congrArg ((G.map φ).f 1) (hcyc K x)).symm.trans hright.symm))
  rw [hcycle]
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (G.map φ) 1) (cyc K x)).symm

-- The original interface includes E, which is irrelevant to this algebraic comparison.
set_option linter.unusedVariables false in
/-- The explicit residue cycle quotient is additively the degree-one homology
of the scalar extension of sections.  This is the algebraic quotient step of
Tag 010V, independent of the geometric derived comparison.
(blueprint: new-picard-residue-quotient-model-homology) -/
theorem picard_residue_quotient_model_homology
    [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    Nonempty (affineResidueCycleHomology W U p K ≃+ C.homology 1) := by
  obtain ⟨e, _⟩ := picard_residue_quotient_model_homology_naturality W w U hwU hU p hp
  exact ⟨e K⟩

end AlgebraicGeometry.Scheme
