/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.SmallInjectivePresheafCechExact
import WeilConjectures.CategoryTheory.SheafCechAugmentationDegreeZero
import Mathlib.Algebra.Homology.SingleHomology

/-!
# The canonical augmented Čech row of an injective sheaf

Source: Stacks Project, Cohomology on Sites, Tags 03AW and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The restriction augmentation of one injective sheaf is a quasi-isomorphism.
The Hom sets, covering index, and abelian group values all have universe v.
Source: Stacks Project, Cohomology on Sites, Tags 03AW and 03F6. -/
theorem injective_cech_augmentation_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{v}]
    (I : Sheaf J AddCommGrpCat.{v}) [Injective I] (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X)
    (e : (CochainComplex.single₀ AddCommGrpCat.{v}).obj (I.obj.obj (op X)) ⟶
      (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj ((Over.forget X).op ⋙ I.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
          I.obj.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op) : QuasiIso e := by
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  refine ⟨fun p ↦ ?_⟩
  cases p with
  | zero => exact sheaf_cech_augmentation_quasiIsoAt_zero I X π hπ e he
  | succ q =>
    rw [quasiIsoAt_iff_exactAt e (q + 1)
      (CochainComplex.exactAt_succ_single_obj _ q)]
    exact small_injective_presheaf_cech_exact I.obj X U π q

end CategoryTheory
