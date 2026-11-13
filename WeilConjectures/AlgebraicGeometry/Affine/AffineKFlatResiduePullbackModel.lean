/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.KFlat
import all WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeComparison
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.Local.LocalKFlatPullbackModel
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-! # An affine K-flat model of the ambient derived residue pullback

Source: Stacks Project, Tags 0BDI and 08DW(2).
-/

@[expose] public section

universe u w
open CategoryTheory
open CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products

private noncomputable def mapComplexComparison
    {C D E H J : Type*} [Category* C] [Category* D] [Category* E]
    [Category* H] [Category* J] [Preadditive C] [Preadditive D] [Preadditive E]
    [Preadditive H] [Preadditive J]
    (A : C ⥤ D) (B : D ⥤ E) (S : C ⥤ H) (R : H ⥤ J) (L : J ⥤ E)
    [A.Additive] [B.Additive] [S.Additive] [R.Additive] [L.Additive]
    (α : A ⋙ B ≅ (S ⋙ R) ⋙ L) (F : CochainComplex C ℤ) :
    (B.mapHomologicalComplex (.up ℤ)).obj ((A.mapHomologicalComplex (.up ℤ)).obj F) ≅
      (L.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj ((S.mapHomologicalComplex (.up ℤ)).obj F)) :=
  (NatIso.mapHomologicalComplex α (.up ℤ)).app F

-- The natural comparisons involve several composed functors on sheaves and complexes.
/-- A supplied K-flat affine module model computes the ambient derived residue pullback
as an object, before taking any cohomology or dimensions. The scalar field is transported
by the explicitly constructed residue-field isomorphism `e`.

Source: Stacks Project, Tag 0BDI, affine reduction; Tag 08DW(2), affine derived pullback. -/
theorem affine_kFlat_residuePullback_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (U : X.Opens) (hU : IsAffineOpen U)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (hF : (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.obj (.op U))) (.up ℤ)).kFlat F)
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj F)))
    (z : U) :
    let e := asIso (U.ι.residueFieldMap z) ≪≫
      (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫
        Spec.residueFieldIso (X.presheaf.obj (.op U)) (hU.isoSpec.hom z)
    Nonempty ((derivedPullback (X.fromSpecResidueField z)).obj E ≅
      DerivedCategory.Q.obj
        (((tilde.functor (X.residueField z)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars e.hom.hom).mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.extendScalars
              (algebraMap (X.presheaf.obj (.op U))
                (hU.isoSpec.hom z).asIdeal.ResidueField)).mapHomologicalComplex
                  (.up ℤ)).obj F)))) := by
  classical
  let A := X.presheaf.obj (.op U)
  let p := hU.isoSpec.hom z
  let e := asIso (U.ι.residueFieldMap z) ≪≫
    (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫ Spec.residueFieldIso A p
  let ψ := algebraMap A p.asIdeal.ResidueField
  let φ := (CommRingCat.ofHom ψ ≫ e.inv).hom
  let g : Spec (X.residueField z) ⟶ U.toScheme :=
    Spec.map (asIso (U.ι.residueFieldMap z)).inv ≫ U.toScheme.fromSpecResidueField z
  have hg : g ≫ U.ι = X.fromSpecResidueField z := by
    dsimp [g]
    rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp
  have hchart : g ≫ hU.isoSpec.hom = Spec.map (CommRingCat.ofHom φ) := by
    dsimp [g, φ, e, ψ, p]
    rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp, Category.assoc]
    rfl
  let T := tilde.functor A
  let R := Modules.restrictFunctor hU.isoSpec.hom
  let V := (Modules.overEquiv U).functor
  let B := (Modules.overEquiv U).inverse
  have : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : R.Additive := Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
  have : (affinePerfectSheafification X U hU).Additive := by
    unfold affinePerfectSheafification
    infer_instance
  let K := ((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj F
  let P := (T.mapHomologicalComplex (.up ℤ)).obj F
  have hP : CochainComplex.IsKFlatTensor (R := (Spec A).sheaf) P := by
    apply isKFlat_tilde A F
    intro G hG
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient _ (.up ℤ)).obj F)).mp
        ((HomotopyCategory.kFlat_quotient_obj_iff F).mpr hF)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic G).mpr hG)).2
  have : (Modules.tensorPullback hU.isoSpec.hom).Additive :=
    (Modules.nonempty_tensorPullbackAdjunction _).some.left_adjoint_additive
  let θ : Modules.tensorPullback hU.isoSpec.hom ≅ R :=
    (Modules.nonempty_tensorPullbackAdjunction _).some.leftAdjointUniq
      (Modules.restrictAdjunction _)
  have hRP : CochainComplex.IsKFlatTensor (R := U.toScheme.sheaf)
      ((R.mapHomologicalComplex (.up ℤ)).obj P) := by
    have h := CochainComplex.isKFlat_pullback hU.isoSpec.hom.base U.toScheme.sheaf
      (Spec A).sheaf ⟨hU.isoSpec.hom.c⟩ P hP
    apply Modules.kFlat_of_iso ((NatIso.mapHomologicalComplex θ (.up ℤ)).app P)
    convert h using 1
    rfl
  let δ : affinePerfectSheafification X U hU ⋙ V ≅ T ⋙ R :=
    Functor.associator T (R ⋙ B) V ≪≫
      Functor.isoWhiskerLeft T (Functor.associator R B V) ≪≫
      Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft R (Modules.overEquiv U).counitIso) ≪≫
      Functor.isoWhiskerLeft T (Functor.rightUnitor R)
  let ε : (V.mapHomologicalComplex (.up ℤ)).obj K ≅
      (R.mapHomologicalComplex (.up ℤ)).obj P :=
    (NatIso.mapHomologicalComplex δ (.up ℤ)).app F
  have hK := Modules.kFlat_of_iso ε.symm hRP
  obtain ⟨q⟩ := derivedPullback_local_kFlat_model
    (X.fromSpecResidueField z) U g hg E K hK hmodel
  let η : ModuleCat.extendScalars e.inv.hom ≅ ModuleCat.restrictScalars e.hom.hom :=
    (ModuleCat.extendRestrictScalarsAdj e.inv.hom).leftAdjointUniq
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.commRingCatIsoToRingEquiv).toAdjunction
  have : (ModuleCat.extendScalars ψ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ψ).left_adjoint_additive
  let σ : ModuleCat.extendScalars φ ≅
      ModuleCat.extendScalars ψ ⋙ ModuleCat.restrictScalars e.hom.hom :=
    ModuleCat.extendScalarsComp ψ e.inv.hom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars ψ) η
  let L := tilde.functor (X.residueField z)
  have : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let τ : Modules.tensorPullback f ≅ Modules.pullback f :=
    (Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction f)
  obtain ⟨β, _⟩ := Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ)
  let α : affinePerfectSheafification X U hU ⋙ (V ⋙ Modules.pullback g) ≅
      (ModuleCat.extendScalars ψ ⋙ ModuleCat.restrictScalars e.hom.hom) ⋙ L :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight δ (Modules.pullback g) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft T (Modules.restrictFunctorIsoPullback hU.isoSpec.hom)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft T (Modules.pullbackComp g hU.isoSpec.hom) ≪≫
      Functor.isoWhiskerLeft T (Modules.pullbackCongr hchart) ≪≫
      Functor.isoWhiskerLeft T τ.symm ≪≫ β ≪≫ Functor.isoWhiskerRight σ L
  exact ⟨q ≪≫ DerivedCategory.Q.mapIso
    (mapComplexComparison (affinePerfectSheafification X U hU) (V ⋙ Modules.pullback g)
      (ModuleCat.extendScalars ψ) (ModuleCat.restrictScalars e.hom.hom) L α F)⟩

end AlgebraicGeometry.Scheme
