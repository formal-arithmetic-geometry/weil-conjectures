/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Coherent ordinary scalar extension

## References

* Stacks Project, Tags 03CZ, 03D7, 03EK, 06YT, 0FND
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- A scalar adjunction evaluates on a local pure tensor by scalar multiplication of
its transpose. -/
theorem systemScalarModel_transpose_tmul {R S : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ S} (A : SystemScalarModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (M : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f : A.model.E.obj P ⟶ M) (U : Cᵒᵖ) (c : S.obj.obj U) (x : P.val.obj U) :
    f.val.app U (systemModelTmul A.model P U c x) =
      c • (show M.val.obj U from (A.ordinaryAdj.homEquiv P M f).val.app U x) := by
  have hu := A.unit_normalized P U x
  dsimp only [systemModelTmul] at hu ⊢
  rw [one_smul] at hu
  rw [← hu]
  rw [Adjunction.homEquiv_unit]
  change (f.val.app U).hom (c • _) = c • ((f.val.app U).hom _)
  exact (f.val.app U).hom.map_smul c _

/-- Restriction along a composite is successive restriction, with identity section maps. -/
def systemScalarRestrictionComposition {R S T : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (γ : R ⟶ T) (hγ : γ = φ ≫ ψ) :
    (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map ψ)) ⋙ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) ≅ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map γ)) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (φ.hom.app U).hom (ψ.hom.app U).hom
        (γ.hom.app U).hom (congrArg (fun f ↦ (f.hom.app U).hom) hγ)
        (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

/-- Ordinary scalar-extension composition, determined by the restriction adjunctions. -/
def systemScalarModelComposition {R S T : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T} (hγ : γ = φ ≫ ψ)
    (A : SystemScalarModel φ) (B : SystemScalarModel ψ) (D : SystemScalarModel γ) :
    A.model.E ⋙ B.model.E ≅ D.model.E :=
  Adjunction.leftAdjointUniq
    ((A.ordinaryAdj.comp B.ordinaryAdj).ofNatIsoRight
      (systemScalarRestrictionComposition φ ψ γ hγ)) D.ordinaryAdj

/-- The ordinary associator multiplies the two scalar factors. -/
theorem systemScalarModelComposition_tmul {R S T : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T} (hγ : γ = φ ≫ ψ)
    (A : SystemScalarModel φ) (B : SystemScalarModel ψ) (D : SystemScalarModel γ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (c : T.obj.obj U) (d : S.obj.obj U) (x : P.val.obj U) :
    ((systemScalarModelComposition hγ A B D).hom.app P).val.app U
      (systemModelTmul B.model (A.model.E.obj P) U c
        (systemModelTmul A.model P U d x)) =
      systemModelTmul D.model P U (c * (ψ.hom.app U) d) x := by
  let f := (systemScalarModelComposition hγ A B D).hom.app P
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((A.ordinaryAdj.comp B.ordinaryAdj).ofNatIsoRight
      (systemScalarRestrictionComposition φ ψ γ hγ)) D.ordinaryAdj P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  have hx := congrArg (fun g : P ⟶ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map γ)).obj
        (D.model.E.obj P) ↦ g.val.app U x) h
  change ((A.ordinaryAdj.homEquiv P _
    (B.ordinaryAdj.homEquiv _ _ f)).val.app U x) = (D.ordinaryAdj.unit.app P).val.app U x
      at hx
  change f.val.app U _ = _
  have hB := systemScalarModel_transpose_tmul B (A.model.E.obj P) (D.model.E.obj P)
    f U c (systemModelTmul A.model P U d x)
  erw [hB]
  have hA := systemScalarModel_transpose_tmul A P
    ((restrictScalars.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).map ψ)).obj (D.model.E.obj P))
    (B.ordinaryAdj.homEquiv _ _ f) U d x
  erw [hA, hx]
  rw [D.unit_normalized]
  dsimp only [systemModelTmul]
  rw [one_smul]
  exact (mul_smul c (ψ.hom.app U d)
    ((eqToHom (D.model.obj_eq P).symm).val.app U
      ((toSheafify J (changeOfRingsPresheaf γ P).presheaf).app U
        (((ModuleCat.extendRestrictScalarsAdj (γ.hom.app U).hom).unit.app
          (P.val.obj U)) x)))).symm

/-- Restriction along an identity coefficient map is the identity on sections. -/
def systemScalarRestrictionUnit {R : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ R) (hφ : φ = 𝟙 R) :
    restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) ≅
      𝟭 (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      ModuleCat.restrictScalarsId'App (φ.hom.app U).hom
        (congrArg (fun f ↦ (f.hom.app U).hom) hφ) (M.val.obj U))
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

/-- The ordinary tensor unit, determined by the scalar adjunction. -/
def systemScalarModelUnit {R : Sheaf J CommRingCat.{w}} {φ : R ⟶ R}
    (hφ : φ = 𝟙 R) (A : SystemScalarModel φ) :
    A.model.E ≅ 𝟭 (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :=
  Adjunction.leftAdjointUniq
    (A.ordinaryAdj.ofNatIsoRight (systemScalarRestrictionUnit φ hφ)) (Adjunction.id)

/-- The ordinary tensor unit multiplies a local pure tensor. -/
theorem systemScalarModelUnit_tmul {R : Sheaf J CommRingCat.{w}} {φ : R ⟶ R}
    (hφ : φ = 𝟙 R) (A : SystemScalarModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (c : R.obj.obj U) (x : P.val.obj U) :
    ((systemScalarModelUnit hφ A).hom.app P).val.app U
      (systemModelTmul A.model P U c x) = c • x := by
  let f := (systemScalarModelUnit hφ A).hom.app P
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (A.ordinaryAdj.ofNatIsoRight (systemScalarRestrictionUnit φ hφ)) (Adjunction.id) P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hx := congrArg (fun g : P ⟶ P ↦ g.val.app U x) h
  change (A.ordinaryAdj.homEquiv P P f).val.app U x = x at hx
  change f.val.app U _ = _
  erw [systemScalarModel_transpose_tmul A P P f U c x, hx]

/-- The derived associator is the left-adjoint uniqueness map of the exact restriction
comparison. -/
def systemScalarModelDerivedComposition {R S T : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T} (hγ : γ = φ ≫ ψ)
    (A : SystemScalarModel φ) (B : SystemScalarModel ψ) (D : SystemScalarModel γ) :
    A.model.T ⋙ B.model.T ≅ D.model.T :=
  Adjunction.leftAdjointUniq
    ((A.adjunction.comp B.adjunction).ofNatIsoRight
      (Functor.exactDerivedRestrictionComposition _ _ _
        (systemScalarRestrictionComposition φ ψ γ hγ))) D.adjunction

/-- The derived associator respects the universal comparisons, on every complex. -/
theorem systemScalarModelDerivedComposition_rep {R S T : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ S} {ψ : S ⟶ T} {γ : R ⟶ T} (hγ : γ = φ ≫ ψ)
    (A : SystemScalarModel φ) (B : SystemScalarModel ψ) (D : SystemScalarModel γ)
    (P : CochainComplex
      (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) ℤ) :
    (systemScalarModelDerivedComposition hγ A B D).hom.app (DerivedCategory.Q.obj P) ≫
        D.model.ε.app P =
      B.model.T.map (A.model.ε.app P) ≫
        B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (systemScalarModelComposition hγ A B D)
            (.up ℤ)).hom.app P) := by
  let Rφ := restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  let Rψ := restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map ψ)
  let Rγ := restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map γ)
  let η := systemScalarRestrictionComposition φ ψ γ hγ
  let δ := Functor.exactDerivedRestrictionComposition Rψ Rφ Rγ η
  let ν := systemScalarModelComposition hγ A B D
  let ac := A.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let bc := B.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let dc := D.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let ηc := Functor.mapHomologicalComplexCompIso η (.up ℤ)
  let νc := Functor.mapHomologicalComplexCompIso ν (.up ℤ)
  have hn : ∀ P, (ac.comp bc).homEquiv _ _ (νc.hom.app P) ≫
      ηc.hom.app ((D.model.E.mapHomologicalComplex (.up ℤ)).obj P) = dc.unit.app P := by
    intro P
    apply HomologicalComplex.hom_ext
    intro i
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((A.ordinaryAdj.comp B.ordinaryAdj).ofNatIsoRight η) D.ordinaryAdj (P.X i)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
    change A.ordinaryAdj.homEquiv _ _ (B.ordinaryAdj.homEquiv _ _
      (ν.hom.app (P.X i))) ≫ η.hom.app _ = D.ordinaryAdj.unit.app (P.X i) at h
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h
    rw [Adjunction.homEquiv_unit]
    exact h
  have hρ : ∀ K,
      Rφ.mapDerivedCategoryFactors.inv.app ((Rψ.mapHomologicalComplex (.up ℤ)).obj K) ≫
        Rφ.mapDerivedCategory.map (Rψ.mapDerivedCategoryFactors.inv.app K) ≫
        δ.hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (ηc.hom.app K) ≫ Rγ.mapDerivedCategoryFactors.inv.app K := by
    intro K
    exact Functor.exactDerivedRestrictionComposition_inv_factors Rψ Rφ Rγ η K
  have hcomp := normalizedAdjunction_composition ac bc A.adjunction B.adjunction
    A.model.ε B.model.ε Rφ.mapDerivedCategoryFactors.inv Rψ.mapDerivedCategoryFactors.inv
    A.transpose B.transpose
  have h := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q) (ac.comp bc) dc
    (A.adjunction.comp B.adjunction) D.adjunction
    (fun P ↦ B.model.T.map (A.model.ε.app P) ≫
      B.model.ε.app ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P))
    D.model.ε.app
    (fun K ↦ Rφ.mapDerivedCategoryFactors.inv.app ((Rψ.mapHomologicalComplex (.up ℤ)).obj K) ≫
      Rφ.mapDerivedCategory.map (Rψ.mapDerivedCategoryFactors.inv.app K))
    Rγ.mapDerivedCategoryFactors.inv.app
    (by intros P K f; simpa only [Category.assoc] using hcomp P K f)
    D.transpose ηc δ νc.hom.app hn
    (by intro K; simpa only [Category.assoc] using hρ K) P
  have hv : νc.hom.app P =
      (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  rw [hv] at h
  dsimp only [systemScalarModelDerivedComposition, δ, Rφ, Rψ, Rγ, η, ν] at h ⊢
  simpa only [Category.assoc] using h

/-- The derived tensor unit, fixed by the identity restriction adjunction. -/
def systemScalarModelDerivedUnit {R : Sheaf J CommRingCat.{w}} {φ : R ⟶ R}
    (hφ : φ = 𝟙 R) (A : SystemScalarModel φ) :
    A.model.T ≅ 𝟭 (DerivedCategory
      (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))) :=
  Adjunction.leftAdjointUniq
    (A.adjunction.ofNatIsoRight (Functor.exactDerivedRestrictionUnit _
      (systemScalarRestrictionUnit φ hφ))) Adjunction.id

/-- The derived tensor unit respects the universal comparison on every complex. -/
theorem systemScalarModelDerivedUnit_rep {R : Sheaf J CommRingCat.{w}} {φ : R ⟶ R}
    (hφ : φ = 𝟙 R) (A : SystemScalarModel φ)
    (P : CochainComplex
      (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) ℤ) :
    (systemScalarModelDerivedUnit hφ A).hom.app (DerivedCategory.Q.obj P) =
      A.model.ε.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (systemScalarModelUnit hφ A) (.up ℤ)).hom.app P) := by
  let Rφ := restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  let η := systemScalarRestrictionUnit φ hφ
  let δ := Functor.exactDerivedRestrictionUnit Rφ η
  let ν := systemScalarModelUnit hφ A
  let ac := A.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let ηc := NatIso.mapHomologicalComplex η (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let νc := NatIso.mapHomologicalComplex ν (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  have hn : ∀ P, ac.homEquiv _ _ (νc.hom.app P) ≫ ηc.hom.app P = 𝟙 P := by
    intro P
    apply HomologicalComplex.hom_ext
    intro i
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (A.ordinaryAdj.ofNatIsoRight η) Adjunction.id (P.X i)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
    rw [Adjunction.homEquiv_unit]
    exact h
  have h := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    ac Adjunction.id A.adjunction Adjunction.id A.model.ε.app (fun _ ↦ 𝟙 _)
    Rφ.mapDerivedCategoryFactors.inv.app (fun _ ↦ 𝟙 _) A.transpose
    (by
      intros P K f
      simp only [Category.id_comp, Category.comp_id]
      rfl)
    ηc δ νc.hom.app hn (by
      intro K
      simpa only [Category.comp_id] using
        Functor.exactDerivedRestrictionUnit_inv_factors Rφ η K) P
  have hv : νc.hom.app P = (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [νc, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplexIdIso_hom_app_f]
    exact Category.comp_id _
  rw [hv, Category.comp_id] at h
  dsimp only [systemScalarModelDerivedUnit, δ, Rφ, η, ν] at h ⊢
  exact h

end SheafOfModules
