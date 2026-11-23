/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup

/-!
# Common refinements of admissible blow-ups

Finitely many `U`-admissible blow-ups of a scheme `X` admit a common `U`-admissible blow-up:
the blow-up of the product of the centers dominates each of them, since the inverse image of each
factor of an invertible product ideal is invertible
(`Scheme.IdealSheafData.IsInvertible.of_mul_left`) and the universal property of blowing up
(`Scheme.IdealSheafData.exists_lift_blowup`) applies.

## Main results

- `AlgebraicGeometry.IsAdmissible.exists_common_blowup`: blueprint
  `lemma-products-composites-u-admissible-blow--1`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Finitely many `U`-admissible blow-ups admit a common `U`-admissible blow-up** (blueprint
`lemma-products-composites-u-admissible-blow--1`): for a finite family of `U`-admissible centers
`B i` on `X`, there is a `U`-admissible center `B'` whose blow-up dominates each blow-up of
`B i` over `X`. One takes for `B'` the product of the centers. -/
theorem IsAdmissible.exists_common_blowup {X : Scheme.{u}} {U : X.Opens} {ι : Type*} [Finite ι]
    (B : ι → IsAdmissible X U) :
    ∃ B' : IsAdmissible X U, ∀ i, ∃ f : B'.I.blowup ⟶ (B i).I.blowup,
      f ≫ (B i).I.blowupMap = B'.I.blowupMap := by
  classical
  have := Fintype.ofFinite ι
  let B' : IsAdmissible X U :=
    { I := ∏ i, (B i).I
      finiteType := Finset.prod_induction _ _ (fun _ _ ha hb ↦ ha.mul hb)
        (by simpa using Scheme.IdealSheafData.ofFiniteType_top) fun i _ ↦ (B i).finiteType
      disjoint_support := by
        refine Finset.prod_induction _
          (fun J : X.IdealSheafData ↦ Disjoint (U : Set X) (J.support : Set X))
          (fun a b ha hb ↦ ?_) (by simp) fun i _ ↦ (B i).disjoint_support
        rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
        exact Set.disjoint_union_right.mpr ⟨ha, hb⟩ }
  refine ⟨B', fun i ↦ (B i).I.exists_lift_blowup ?_⟩
  refine Scheme.IdealSheafData.IsInvertible.of_mul_left
    (K₂ := (∏ i' ∈ Finset.univ.erase i, (B i').I).comap B'.I.blowupMap) ?_
  rw [← Scheme.IdealSheafData.comap_mul,
    Finset.mul_prod_erase Finset.univ (fun i ↦ (B i).I) (Finset.mem_univ i)]
  exact B'.I.isInvertible_comap_blowupMap

end AlgebraicGeometry
