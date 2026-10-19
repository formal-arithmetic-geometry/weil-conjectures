/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedFiberOpenFactorization
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.ResidueTildeHomologyComparison
import Sheaf.AlgebraicGeometry.AffinePerfectSectionsCounit
import Sheaf.AlgebraicGeometry.AffineResidueScalarTransport
import all Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import all Sheaf.AlgebraicGeometry.LocalizedStrictPerfectResidueHomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Natural derived pullback calculation on strictly perfect affine complexes

Source: Stacks Project, Tags 01IB, 08DW and 06YJ.
(blueprint: new-affine-perfect-residue-model-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Functor.additive_of_preserves_binary_products

private theorem residueTermComparison (W : Scheme.{v}) (w : W) (U : W.Opens)
    (hwU : w ∈ U) (hU : IsAffineOpen U) :
    let V : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
      (Modules.overEquiv U).functor
    Nonempty (affinePerfectSheafification W U hU ⋙
      (V ⋙ Modules.pullback (openResiduePoint W w U hwU)) ≅
        ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom ⋙
          tilde.functor (W.residueField w)) := by
  classical
  dsimp only
  let A := W.presheaf.obj (.op U)
  let z : U := ⟨w, hwU⟩
  let p := hU.isoSpec.hom z
  let e := asIso (U.ι.residueFieldMap z) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫ Spec.residueFieldIso A p
  let ψ := algebraMap A p.asIdeal.ResidueField
  let φ := (CommRingCat.ofHom ψ ≫ e.inv).hom
  let g := openResiduePoint W w U hwU
  have hchart : g ≫ hU.isoSpec.hom = Spec.map (CommRingCat.ofHom φ) := by
    dsimp [g, openResiduePoint, φ, e, ψ, p, z]
    rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp, Category.assoc]
    rfl
  let TA := tilde.functor A
  let RC := Modules.restrictFunctor hU.isoSpec.hom
  let V := (Modules.overEquiv U).functor
  let B := (Modules.overEquiv U).inverse
  let Sh := affinePerfectSheafification W U hU
  let δ : Sh ⋙ V ≅ TA ⋙ RC :=
    Functor.associator TA (RC ⋙ B) V ≪≫
      Functor.isoWhiskerLeft TA (Functor.associator RC B V) ≪≫
      Functor.isoWhiskerLeft TA
        (Functor.isoWhiskerLeft RC (Modules.overEquiv U).counitIso) ≪≫
      Functor.isoWhiskerLeft TA (Functor.rightUnitor RC)
  let η : ModuleCat.extendScalars e.inv.hom ≅ ModuleCat.restrictScalars e.hom.hom :=
    (ModuleCat.extendRestrictScalarsAdj e.inv.hom).leftAdjointUniq
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.commRingCatIsoToRingEquiv).toAdjunction
  let S := ModuleCat.extendScalars.{v, v, v} ψ
  let R := ModuleCat.restrictScalars.{v, v, v} e.hom.hom
  let σ : ModuleCat.extendScalars φ ≅ S ⋙ R :=
    ModuleCat.extendScalarsComp ψ e.inv.hom ≪≫ Functor.isoWhiskerLeft S η
  let L := tilde.functor (W.residueField w)
  let f := Spec.map (CommRingCat.ofHom φ)
  let τ : Modules.tensorPullback f ≅ Modules.pullback f :=
    (Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction f)
  obtain ⟨β, _⟩ := Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ)
  obtain ⟨δs⟩ := affine_residue_scalar_transport W U hU z
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight δ (Modules.pullback g) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft TA (Modules.restrictFunctorIsoPullback hU.isoSpec.hom)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft TA (Modules.pullbackComp g hU.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft TA (Modules.pullbackCongr hchart) ≪≫
    Functor.isoWhiskerLeft TA τ.symm ≪≫ β ≪≫
    Functor.isoWhiskerRight σ L ≪≫ Functor.isoWhiskerRight δs L⟩

variable
  [∀ Y : Scheme.{v},
    HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
  [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
    (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

set_option maxHeartbeats 500000 in
-- The natural comparison traverses complex, homotopy and derived localization functors.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Termwise residue extension computes local derived fibre cohomology naturally
on every strictly perfect complex. Source: Stacks Project, Tags 01IB, 08DW and 06YJ.
(blueprint: new-affine-perfect-residue-model-naturality)

Proof: Work in the full subcategory of strictly perfect complexes. Transport each
complex by the canonical over-site equivalence. Boundedness and finite-free
retractions imply K-flatness, so the chosen derived-pullback counit is invertible
on this whole subcategory. Compute its ordinary pullback by the natural affine
associated-sheaf/base-change formula, using the natural terminal-section
reconstruction counit. The canonical field transport makes the coefficient map
exactly section evaluation. Take homology and global sections on the residue
spectrum; these sections are exact and undo associated sheaves. All factors
are natural isomorphisms on the full subcategory, giving the stated family and
its equation for every chain map. -/
theorem affine_perfect_residue_model_naturality
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
    let P : ObjectProperty (CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :=
      IsStrictlyPerfect W U
    Nonempty (P.ι ⋙ G ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w)) (.up ℤ) 1 ≅
      P.ι ⋙ DerivedCategory.Q ⋙ localDerivedFiberCohomologyFunctor W w U hwU 1) := by
  dsimp only
  classical
  let D := SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)
  let A := SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace)
  let B := SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)
  let P : ObjectProperty (CochainComplex D ℤ) := IsStrictlyPerfect W U
  let ι := P.ι
  let V : D ⥤ A := (Modules.overEquiv U).functor
  have : V.IsEquivalence := by
    set_option backward.isDefEq.respectTransparency false in
      exact (Modules.overEquiv U).isEquivalence_functor
  have : Limits.PreservesFiniteLimits V := inferInstance
  have : Limits.PreservesFiniteColimits V := inferInstance
  have : V.Additive := by
    set_option backward.isDefEq.respectTransparency false in
      exact Functor.additive_of_preserves_binary_products _
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let g := openResiduePoint W w U hwU
  obtain ⟨hEadd, ε, _, hflat⟩ := tensorDerivedCounit g
  let E : A ⥤ B := Modules.tensorPullback g
  have : E.Additive := hEadd
  let Ec := E.mapHomologicalComplex (.up ℤ)
  have hε : IsIso (Functor.whiskerLeft
      ((ι ⋙ Vc) ⋙ HomotopyCategory.quotient A (.up ℤ)) ε) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro K
    exact hflat (Vc.obj K.obj) (strictlyPerfect_overEquiv_isKFlat W U K.obj K.property)
  have := hε
  obtain ⟨c⟩ : Nonempty ((ι ⋙ Vc) ⋙ DerivedCategory.Q.{v + 1} ⋙ derivedPullback g ≅
      (ι ⋙ Vc) ⋙ Ec ⋙ DerivedCategory.Q.{v + 1}) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact counitComparison E (derivedPullback g) (ι ⋙ Vc) ε
  let PG : A ⥤ B := Modules.pullback g
  have : PG.Additive := Modules.instAdditivePullback g
  let J : D ⥤ B := V ⋙ PG
  have : J.Additive := inferInstanceAs (V ⋙ PG).Additive
  let τ : E ≅ PG :=
    (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
  obtain ⟨c'⟩ : Nonempty (ι ⋙ DerivedCategory.Q ⋙ V.mapDerivedCategory ⋙
      derivedPullback g ≅ ι ⋙ J.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact ⟨Functor.isoWhiskerLeft ι (Functor.isoWhiskerRight V.mapDerivedCategoryFactors
        (derivedPullback g)) ≪≫ c ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft (ι ⋙ Vc)
          (NatIso.mapHomologicalComplex τ (.up ℤ))) DerivedCategory.Q ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft ι
          (Functor.mapHomologicalComplexCompIso (Iso.refl (V ⋙ PG)) (.up ℤ)))
            DerivedCategory.Q⟩
  let F : D ⥤ ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  have : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  have : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
  let Sh := affinePerfectSheafification W U hU
  have : Sh.Additive := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      let TA := tilde.functor Γ(W, U)
      have : TA.Additive := ⟨by intros; exact tilde.map_add _ _⟩
      let RC := Modules.restrictFunctor hU.isoSpec.hom
      have : RC.Additive :=
        Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
      have : (Modules.overEquiv U).inverse.Additive :=
        Functor.additive_of_preserves_binary_products _
      dsimp only [Sh, affinePerfectSheafification]
      infer_instance
  let L : ModuleCat.{v} (W.residueField w) ⥤ B := tilde.functor (W.residueField w)
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  obtain ⟨ρ, hρ⟩ := affine_perfect_sections_counit W U hU
  have : IsIso (Functor.whiskerLeft ι ρ) :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun K ↦ hρ K.obj K.property)
  obtain ⟨α'⟩ := residueTermComparison W w U hwU hU
  let α : Sh ⋙ J ≅ T ⋙ L := by
    set_option backward.isDefEq.respectTransparency false in exact α'
  let r := asIso (Functor.whiskerLeft ι ρ)
  obtain ⟨a⟩ : Nonempty (ι ⋙ J.mapHomologicalComplex (.up ℤ) ≅
      ι ⋙ G ⋙ L.mapHomologicalComplex (.up ℤ)) :=
    ⟨Functor.isoWhiskerRight r.symm (J.mapHomologicalComplex (.up ℤ)) ≪≫
      Functor.isoWhiskerLeft (ι ⋙ F.mapHomologicalComplex (.up ℤ))
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (Sh ⋙ J)) (.up ℤ)) ≪≫
          NatIso.mapHomologicalComplex α (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ L)) (.up ℤ)).symm)⟩
  obtain ⟨d⟩ : Nonempty (ι ⋙ DerivedCategory.Q ⋙ V.mapDerivedCategory ⋙
      derivedPullback g ≅ ι ⋙ G ⋙ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    ⟨c' ≪≫ Functor.isoWhiskerRight a DerivedCategory.Q⟩
  let Γ : B ⥤ ModuleCat.{v} (W.residueField w) :=
    moduleSpecΓFunctor (R := W.residueField w)
  let H := DerivedCategory.homologyFunctor B 1
  let HM := HomologicalComplex.homologyFunctor (ModuleCat.{v} (W.residueField w)) (.up ℤ) 1
  obtain ⟨β⟩ : Nonempty ( ι ⋙ DerivedCategory.Q ⋙ localDerivedFiberCohomologyFunctor W w U hwU 1 ≅
      ι ⋙ G ⋙ HM) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      exact ⟨Functor.isoWhiskerLeft (ι ⋙ DerivedCategory.Q)
        (eqToIso (localDerivedFiberCohomologyFunctor_eq W w U hwU 1)) ≪≫
        Functor.isoWhiskerRight d (H ⋙ Γ) ≪≫
          Functor.isoWhiskerLeft (ι ⋙ G)
            (residueTildeHomologyComparison (W.residueField w)
              (Field.toIsField (W.residueField w)) 1)⟩
  exact ⟨β.symm⟩

end
end AlgebraicGeometry.Scheme
