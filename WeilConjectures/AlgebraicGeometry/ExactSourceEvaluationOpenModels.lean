/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationPostcomposition
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Ordinary models for evaluation on the open scheme

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory


attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU. -/
local instance modelsEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

private theorem tensor_quasiIso_of_isKFlat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R : Sheaf J CommRingCat.{u}}
    {M M' D : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (t : M ⟶ M') (ht : QuasiIso t) (hD : D.IsKFlatTensor) :
    QuasiIso (HomologicalComplex.mapBifunctorMap t (𝟙 D) (curriedTensor _) (.up ℤ)) := by
  let : MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    Classical.choice (SheafOfModules.tensorClosed R).1
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic t).1 ht
  have hd := hD (CochainComplex.mappingCone t) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (hd i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso t D (curriedTensor _))

private theorem comparison_of_resolution_square
    {C : Type*} [Category* C] {S H T T' V V' : C}
    (g : S ⟶ H) (f : T ⟶ V) (f' : T' ⟶ V') (t : T ≅ T') (h : V ≅ V')
    (a' : S ≅ T') (b' : H ≅ V')
    (hg : g ≫ b'.hom = a'.hom ≫ f') (hs : t.hom ≫ f' = f ≫ h.hom) :
    ∃ a : S ≅ T, ∃ b : H ≅ V, g ≫ b.hom = a.hom ≫ f := by
  refine ⟨a' ≪≫ t.symm, b' ≪≫ h.symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hg]
  apply (cancel_mono h.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hs]
  simp only [Iso.inv_hom_id_assoc]

set_option maxHeartbeats 400000 in
-- The localized comparison elaborates the sheaf tensor and Hom structures together.
/-- The ordinary evaluation calculation, entirely on the open scheme. The functor E
only changes from the over-site to its equivalent scheme site; it does not restrict
an object or an evaluation arrow from X (Stacks, Tags 08DJ, 08DM, 08DQ). -/
theorem exists_exactSource_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (hdual : (localEvaluationDual X U P).IsKFlatTensor)
    (_eK : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ K)
    (_eN : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F) ≅ N)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) D K
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ E.obj (DerivedCategory.Q.obj (localEvaluationTensor X U P F)),
      ∃ b : H.obj (op K, N) ≅
          E.obj (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F)),
        g ≫ b.hom = a.hom ≫ E.map (DerivedCategory.Q.map f) := by
  classical
  let A := localEvaluationModules X U
  let : HasDerivedCategory.{w} A := (inferInstance : HasDerivedCategory.{w}
    (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
  let Q := DerivedCategory.Q.{w} (C := A)
  let E := (Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)).mapDerivedCategory
  let H := derivedInternalHom
    (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
  let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
  let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
    ((α_ N D K).hom ≫ N ◁
      ((schemeDerivedTensorHomEquiv U.toScheme) D K
        (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
  change ∃ a : N ⊗ D ≅ E.obj (Q.obj (localEvaluationTensor X U P F)),
    ∃ b : H.obj (op K, N) ≅ E.obj (Q.obj (homComplex (R := X.sheaf.over U) P F)),
      g ≫ b.hom = a.hom ≫ E.map (Q.map f)
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj F
  let η : F ⟶ I := (CochainComplex.toKInjectiveResolution.{u} A).app F
  have hη : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A F).2
  have : QuasiIso η := hη
  have : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A F
  let fI : localEvaluationTensor X U P I ⟶ homComplex (R := X.sheaf.over U) P I :=
    { f := localEvaluationDegreeMap X U P I
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P I n m h }
  have hfI : IsLocalOrdinaryEvaluation X U P I fI := by
    intro p q n r h
    exact localEvaluationDegreeMap_formula X U P I p q n r h
  let t := HomologicalComplex.mapBifunctorMap η (𝟙 (localEvaluationDual X U P))
    (curriedTensor _) (.up ℤ)
  let h := ((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map η
  have : QuasiIso h := hhom F I η hη
  have : QuasiIso t :=
    tensor_quasiIso_of_isKFlat (R := X.sheaf.over U) η hη hdual
  have : IsIso (E.map (Q.map t)) := inferInstance
  have : IsIso (E.map (Q.map h)) := inferInstance
  let eI : E.obj (Q.obj I) ≅ N := (E.mapIso (asIso (Q.map η))).symm ≪≫ _eN
  have hmodel := exists_exactSource_kInjective_evaluation_open_models
    X U K N P I hhom hdual _eK eI fI hfI
  change ∃ a : N ⊗ D ≅ E.obj (Q.obj (localEvaluationTensor X U P I)),
    ∃ b : H.obj (op K, N) ≅ E.obj (Q.obj (homComplex (R := X.sheaf.over U) P I)),
      g ≫ b.hom = a.hom ≫ E.map (Q.map fI) at hmodel
  obtain ⟨aI, bI, habI⟩ := hmodel
  have hs := ordinaryEvaluation_postcomposition X U P F I η f fI _hf hfI
  have hs' : E.map (Q.map t) ≫ E.map (Q.map fI) =
      E.map (Q.map f) ≫ E.map (Q.map h) := by
    simpa only [Functor.map_comp] using congrArg (fun z ↦ E.map (Q.map z)) hs
  exact comparison_of_resolution_square g (E.map (Q.map f)) (E.map (Q.map fI))
    (asIso (E.map (Q.map t))) (asIso (E.map (Q.map h))) aI bI habI hs'

end AlgebraicGeometry
