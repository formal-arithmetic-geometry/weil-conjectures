/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Presentable.Type
public import WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# `κ`-presented modules are `κ`-presentable

Let `κ` be a regular cardinal and `R` a ring. We show that a `κ`-presented `R`-module, i.e. a
cokernel of a linear map `R^(S') ⟶ R^(S)` with `S` and `S'` of cardinality `< κ`, is a
`κ`-presentable object of `ModuleCat R`. In particular, if `R` has cardinality `< κ`, then every
`R`-module of cardinality `< κ` is `κ`-presentable.

The proof uses no element-chasing: the forgetful functor `ModuleCat R ⥤ Type` preserves
filtered colimits, so the free module functor, its left adjoint, sends `κ`-presentable types to
`κ`-presentable modules; and `κ`-presentable objects are closed under cokernels.

## Main results

- `ModuleCat.isCardinalPresentable_of_isColimit_cokernelCofork`: a `κ`-presented module is
  `κ`-presentable.
- `ModuleCat.isCardinalPresentable_of_hasCardinalLT`: a module of cardinality `< κ` over a ring
  of cardinality `< κ` is `κ`-presentable.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R] {κ : Cardinal.{u}} [Fact κ.IsRegular]

instance : (forget (ModuleCat.{u} R)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

/-- The free module `R^(S)` on a type `S` of cardinality `< κ` is `κ`-presentable. -/
lemma isCardinalPresentable_free_obj {S : Type u} (hS : HasCardinalLT S κ) :
    IsCardinalPresentable ((free R).obj S) κ :=
  have := hS.isCardinalPresentable
  (adj R).isCardinalPresentable_leftAdjoint_obj κ S

/-- A `κ`-presented module, i.e. a cokernel of a linear map `R^(S') ⟶ R^(S)` with `S` and `S'`
of cardinality `< κ`, is `κ`-presentable. -/
lemma isCardinalPresentable_of_isColimit_cokernelCofork {S S' : Type u}
    (hS : HasCardinalLT S κ) (hS' : HasCardinalLT S' κ) {f : (free R).obj S' ⟶ (free R).obj S}
    {c : CokernelCofork f} (hc : IsColimit c) :
    IsCardinalPresentable c.pt κ := by
  have := isCardinalPresentable_free_obj (R := R) hS
  have := isCardinalPresentable_free_obj (R := R) hS'
  have (j : WalkingParallelPair) : IsCardinalPresentable ((parallelPair f 0).obj j) κ := by
    cases j <;> assumption
  exact isCardinalPresentable_of_isColimit _ hc κ
    (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))

/-- If `κ` is a regular cardinal, `R` is a ring of cardinality `< κ` and `M` is an `R`-module
of cardinality `< κ`, then `M` is a `κ`-presentable object of `ModuleCat R`. -/
lemma isCardinalPresentable_of_hasCardinalLT {M : ModuleCat.{u} R}
    (hR : HasCardinalLT R κ) (hM : HasCardinalLT M κ) :
    IsCardinalPresentable M κ := by
  have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
  -- `M` is the cokernel of `R^(K) ⟶ R^(M)`, where `K` is the kernel of `R^(M) ⟶ M`
  let p : (free R).obj M ⟶ M := freeDesc (𝟙 _)
  have : Epi p := (epi_iff_surjective p).2 fun x ↦ ⟨freeMk x, freeDesc_apply _ x⟩
  let q : (free R).obj ↑(kernel p : ModuleCat.{u} R) ⟶ kernel p := freeDesc (𝟙 _)
  have : Epi q := (epi_iff_surjective q).2 fun x ↦ ⟨freeMk x, freeDesc_apply _ x⟩
  have hK : HasCardinalLT (kernel p : ModuleCat.{u} R) κ :=
    (hasCardinalLT_finset hκ (hasCardinalLT_prod' hκ hM hR)).of_injective _
      ((Finsupp.graph_injective _ _).comp
        ((mono_iff_injective (kernel.ι p)).1 inferInstance))
  exact isCardinalPresentable_of_isColimit_cokernelCofork hM hK
    (isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)) q rfl)

end ModuleCat
