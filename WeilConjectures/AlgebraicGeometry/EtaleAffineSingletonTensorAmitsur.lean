/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorCofaces

/-! # Singleton affine tensor-section Čech complexes
Source: Stacks Project, Tag 03P2, affine tensor-product calculation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- The singleton Čech complex of an affine map is its tensor Amitsur complex.
Source: Stacks Project, Tag 03P2, identification before the faithfully-flat exactness argument;
Tag 03OZ, singleton-cover calculation. -/
theorem nonempty_etale_affine_singleton_tensor_amitsur_iso
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    Nonempty (((cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
      ((Over.forget U).op ⋙
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Modules.etaleTensorSectionsSheaf F)).obj)) ≅
      (((forget₂ (ModuleCat.{u} Γ(U.left, ⊤)) AddCommGrpCat.{u}) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
          (Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
            Γ((Modules.tensorPullback U.hom).obj F, ⊤))) := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  obtain ⟨e, he⟩ := exists_singletonTensorDegreeComparison X F U W g hU hW
  have hc := singletonTensorDegreeComparison_coface X F U W g e he
  refine ⟨(HomologicalComplex.Hom.isoOfComponents e ?_).symm⟩
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  change (e i).hom ≫ ((AlgebraicTopology.alternatingCofaceMapComplex _).obj
    (singletonTensorCechCosimplicial X F U W g)).d i (i + 1) =
      (singletonTensorForget U.left).map
        ((Algebra.TensorProduct.amitsurComplex Γ(U.left, ⊤) Γ(W.left, ⊤)
          Γ((Modules.tensorPullback U.hom).obj F, ⊤)).d i (i + 1)) ≫ (e (i + 1)).hom
  simp only [Algebra.TensorProduct.amitsurComplex,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  exact Finset.sum_congr rfl (fun k _ ↦ congrArg (fun f ↦ (-1 : ℤ) ^ k.val • f) (hc i k))

end AlgebraicGeometry.Scheme
