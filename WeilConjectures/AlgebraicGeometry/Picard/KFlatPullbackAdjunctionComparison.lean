/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData

/-! # K-flat computation of the pinned adjunction on chain maps

## References

* Stacks Project, Cohomology, Tags 06YI, 06YJ, and 079W
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem counit_isIso {S S' : Scheme.{u}} (g : S' ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    [(Scheme.Modules.tensorPullback g).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace)))
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso _ (.up ℤ)))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, δ, hδ, _, hK⟩ :=
    (derivedPullback_spec g)
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  have := hε
  have : (derivedPullback g).IsLeftDerivedFunctor δ
      (HomotopyCategory.quasiIso _ (.up ℤ)) := hδ
  have := hK P hP
  let e := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε δ
    (HomotopyCategory.quasiIso _ (.up ℤ))
  have he : e.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      δ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    simp [e, Functor.leftDerivedNatIso]
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Comparing the concrete sheaf adjunctions requires unfolding their chosen instances.
/-- For a K-flat source, the localized ordinary transpose computes the pinned derived
transpose. The comparison is independent of the target complex and the chain map. -/
theorem kFlat_pullback_adjunction_comparison
    [d : ∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S S' : Scheme.{u}} (g : S' ⟶ S) :
    ∃ (_hL : (Scheme.Modules.tensorPullback g).Additive)
      (e : ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
        (_ : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P),
          (DerivedCategory.Q
              (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).obj
              (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) ≅
            (derivedPullback g).obj (DerivedCategory.Q.obj P)),
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P)
        (I : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
        (α : P ⟶ ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj I),
        (DerivedCategory.Q
            (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).map
            ((((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomologicalComplex
                (.up ℤ)).homEquiv _ _).symm α) =
          (e P hP).hom ≫ ((relativeMVAdj g).homEquiv _ _).symm
            (DerivedCategory.Q.map α ≫ (schemeMVDirectImageLocalization g).app I) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf, moduleRings] at *
  let : HasDerivedCategory.{w} S.Modules := d S
  let : HasDerivedCategory.{w} S'.Modules := d S'
  let hL := @Classical.choose _ _ (@exists_derivedPullbackComposition.{u, w} d)
  let ε := (Classical.choose (Classical.choose_spec (exists_derivedPullbackComposition))) g
  have hε := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_derivedPullbackComposition)))) g
  let E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings S'.toRingedSpace) := Scheme.Modules.tensorPullback g
  have : E.Additive := hL g
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ)
  let q' := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) (.up ℤ)
  let uS := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let uT := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace))
  have hεP (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P) : IsIso (ε.app (q.obj P)) :=
    counit_isIso g ε hε P hP
  let e (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P) :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P) ≅
          (derivedPullback g).obj (DerivedCategory.Q.obj P) := by
    have := hεP P hP
    exact (uT.app ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      (asIso (ε.app (q.obj P))).symm ≪≫ (derivedPullback g).mapIso (uS.app P)
  refine ⟨hL g, e, ?_⟩
  intro P hP I α
  let ac := (Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomologicalComplex (.up ℤ)
  let a := (ac.homEquiv _ _).symm α
  apply (cancel_epi (e P hP).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply ((relativeMVAdj g).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  let ah := (Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomotopyCategory (.up ℤ)
  let η := (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit
  have h : (relativeMVAdj g).homEquiv _ _
      (ε.app (q.obj P) ≫ DerivedCategory.Qh.map (q'.map a)) =
      DerivedCategory.Qh.map ((ah.homEquiv _ _) (q'.map a)) ≫ η.app (q'.obj I) := by
    exact Classical.choose_spec (exists_schemeDerivedAdjunction g ε hε)
      (q.obj P) (q'.obj I) (q'.map a)
  have ha : (ah.homEquiv _ _) (q'.map a) = q.map α := by
    rw [Adjunction.homEquiv_apply]
    erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change q.map (ac.unit.app P) ≫ q.map
      (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).map a) = q.map α
    rw [← Functor.map_comp]
    exact congrArg q.map ((ac.homEquiv _ _).apply_symm_apply α)
  rw [ha] at h
  change ((relativeMVAdj g).homEquiv _ _)
    (ε.app (q.obj P) ≫ DerivedCategory.Qh.map (q'.map a)) = _ at h
  dsimp only [e, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, asIso_inv]
  simp only [Category.assoc]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality a]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [asIso_hom]
  rw [← Category.assoc (ε.app (q.obj P))]
  rw [Adjunction.homEquiv_naturality_right]
  erw [h]
  have hf : ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomotopyCategoryFactors
      (.up ℤ)).inv.app I = 𝟙 _ := rfl
  dsimp only [schemeMVDirectImageLocalization]
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.whiskerRight_app, hf, Category.assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end AlgebraicGeometry
