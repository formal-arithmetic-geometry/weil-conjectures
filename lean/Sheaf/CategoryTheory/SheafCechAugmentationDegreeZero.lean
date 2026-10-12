/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The canonical augmented Čech row of an injective sheaf

Source: Stacks Project, Cohomology on Sites, Tags 03AW and 03F6.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Canonical degree-zero descent for the categorical Čech complex of any sheaf.
Source: Stacks Project, Cohomology on Sites, Tag 03AN.
(blueprint: lem-sc-sheaf-cech-augmentation-degree-zero)

Proof: The single complex has zero differentials, hence its degree-zero homology
is I(X). The Čech complex has no incoming differential in degree zero, hence its
homology there is the kernel of d^0. The projection of d^0 to a pair (i,j) is
restriction from j minus restriction from i. A zero cocycle therefore gives
compatible sections on U_i: identify the single-factor product with U_i by its
unique projection, and pull the pair equation along any pair of arrows with equal
composites to X. The sheaf condition gives a unique section on X restricting to
these sections. Conversely, restriction of a section has zero differential by
functoriality. These constructions are additive and mutually inverse. Product
projection uniqueness and he identify the given e.f 0 with this restriction map,
so its homology map is this isomorphism. For an empty covering family the sheaf
condition says I(X) is zero; the same uniqueness argument works without choosing
an index. Neither injectivity nor sheafification is needed. -/
theorem sheaf_cech_augmentation_quasiIsoAt_zero
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasFiniteWidePullbacks C]
    (I : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type v} {U : ι → C} (π : ∀ i, U i ⟶ X)
    (hπ : Sieve.ofArrows U π ∈ J X)
    (e : (CochainComplex.single₀ AddCommGrpCat.{v}).obj (I.obj.obj (op X)) ⟶
      (cechComplexFunctor (fun i ↦ Over.mk (π i))).obj ((Over.forget X).op ⋙ I.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        I.obj.obj (op (∏ᶜ (fun k ↦ Over.mk (π (s k)))).left)) t =
          I.obj.map (∏ᶜ (fun k ↦ Over.mk (π (t k)))).hom.op) : QuasiIsoAt e 0 := by
  sorry

end CategoryTheory
