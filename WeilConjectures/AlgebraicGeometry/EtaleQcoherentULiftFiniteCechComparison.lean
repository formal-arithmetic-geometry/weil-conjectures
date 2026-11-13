/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
import WeilConjectures.AlgebraicGeometry.EtaleAffineOpenCechDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSections
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-! # Lifted étale cohomology computed by a finite affine section complex

Source: Stacks Project, Tag 03P2, separated-case proof, and Tag 03DW (2).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite in
private noncomputable def liftedModuleCechIso
    (X : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → X.Opens) (F : X.Modules) :
    (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
        ((cechComplexFunctor U).obj F.presheafModuleCat)) ≅
      (cechComplexFunctor U).obj (F.presheafModuleCat ⋙
        forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  let T := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let P := F.presheafModuleCat
  refine HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ PreservesProduct.iso T
      (fun y : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l))))) ?_
  rintro k _ rfl
  apply Pi.hom_ext
  intro y
  change Fin (k + 2) → ι at y
  simp only [Category.assoc, PreservesProduct.iso_hom]
  change piComparison T _ ≫ ((cechComplexFunctor U).obj (P ⋙ T)).d k (k + 1) ≫
      TopCat.Presheaf.cechComplexFunctorπ U (P ⋙ T) (k + 1) y =
    T.map (((cechComplexFunctor U).obj P).d k (k + 1)) ≫ piComparison T _ ≫
      TopCat.Presheaf.cechComplexFunctorπ U (P ⋙ T) (k + 1) y
  rw [TopCat.Presheaf.cechComplexFunctor_d_π]
  simp only [TopCat.Presheaf.cechComplexFunctorπ]
  erw [piComparison_comp_π]
  rw [← T.map_comp]
  erw [TopCat.Presheaf.cechComplexFunctor_d_π]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum,
    Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro a _
  erw [← Category.assoc, piComparison_comp_π]
  rw [T.map_comp]
  rfl

/-- The lifted associated étale sheaf is computed by the lifted module section
Čech complex of any finite affine open cover of a separated scheme, in positive degree.
Source: Stacks Project, Tag 03P2, separated-case proof, and Tag 03DW (2). -/
theorem nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Nonempty (Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (etaleTensorSectionsSheaf F)) (n + 1) ≃+
      (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
          ((cechComplexFunctor U).obj F.presheafModuleCat)).homology (n + 1)) := by
  classical
  let : EssentiallySmall.{u + 1} X.Etale := essentiallySmallSelf.{0} _
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1} _ _
  let G := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf F)
  obtain ⟨i, hi, hc, hl, ⟨ht⟩, _⟩ := zariski_to_etale_core X
  let : CategoryTheory.Limits.PreservesFiniteLimits i := hl
  obtain ⟨hB, hcofinal⟩ := Scheme.finiteAffineEtaleCechCover_basis X
  have hvan := Scheme.isZero_rightDerived_etale_of_cech_vanishing X
    {W | IsAffine W.left} (Scheme.finiteAffineEtaleCechCover X) G
    (fun _ _ _ _ hf ↦ hf.2.2.2) hB hcofinal
    (fun W I V f hf p hp ↦
      Scheme.isZero_etaleTensorSectionsSheaf_ulift_cech X F W I V f hf p hp)
  obtain ⟨eH⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology (i.obj ⊤) ht G n
  obtain ⟨eC⟩ := Scheme.nonempty_rightDerived_etale_affineOpenCech
    X i hi hc ht U hU hcover G hvan (n + 1)
  obtain ⟨eS⟩ := nonempty_etaleTensor_openSections_iso X i hi F
  let eL := (Functor.associator i.op (etaleTensorSectionsPresheaf F)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).symm ≪≫
    Functor.isoWhiskerRight eS AddCommGrpCat.uliftFunctor.{u + 1, u} ≪≫
    Functor.associator F.presheafModuleCat
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})
      AddCommGrpCat.uliftFunctor.{u + 1, u}
  let eK := (cechComplexFunctor U).mapIso eL ≪≫ (liftedModuleCechIso X U F).symm
  exact ⟨eH.trans (eC.addCommGroupIsoToAddEquiv.trans
    (HomologicalComplex.homologyMapIso eK (n + 1)).addCommGroupIsoToAddEquiv)⟩

end AlgebraicGeometry.Scheme.Modules
