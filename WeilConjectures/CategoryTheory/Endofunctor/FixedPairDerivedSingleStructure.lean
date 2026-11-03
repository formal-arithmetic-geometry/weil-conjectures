/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Frobenius structure on a single fixed-pair module

Source: lem-fix-weil-operations.proof.md, paragraph 3, coefficient twists.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- The derived Frobenius on a single fixed pair is its module Frobenius placed
in degree zero, through the canonical exact forgetting comparison.

Source: lem-fix-weil-operations.proof.md, paragraph 3, actual root-line twists
(blueprint: lem-weil-single-structure-normalization).

Proof: compatibility of exact derived functor composition with degree-zero
embeddings identifies the first two comparisons with the single comparison for
composite forgetting and F. Naturality of the single comparison for the structure
natural isomorphism then gives the formula. Cancel the composition comparison.
No constructibility or nonzero-object hypothesis is used. -/
theorem derived_single_structure (M : IsoAlgebra F) :
    F.mapDerivedCategory.map (((forget F).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app M.carrier ≫
      (DerivedCategory.singleFunctor C 0).map M.str.hom =
    (((Functor.mapDerivedCategoryCompIso (forget F) F).symm ≪≫
      Functor.mapDerivedCategoryNatIso (strNatIso F)).hom.app
        ((DerivedCategory.singleFunctor (IsoAlgebra F) 0).obj M)) ≫
      ((forget F).mapDerivedCategorySingleFunctor 0).hom.app M := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (forget F) F).hom.app
    ((DerivedCategory.singleFunctor (IsoAlgebra F) 0).obj M))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hcomp := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor (forget F) F M
  have hnat := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor (strNatIso F) M
  simpa only [forget_obj, Category.assoc] using
    (congrArg (fun f ↦ f ≫ (DerivedCategory.singleFunctor C 0).map M.str.hom)
      hcomp).trans hnat.symm

end CategoryTheory.Endofunctor.IsoAlgebra
