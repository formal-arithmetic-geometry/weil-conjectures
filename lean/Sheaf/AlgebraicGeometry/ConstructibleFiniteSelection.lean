/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Finite selection of geometric stalk tests

Source: smooth purity blueprint, unit `sk-prop-sf-cbc`, order 1604;
Stacks Project, Tag 09Z6, partition argument
(blueprint: lem-weil-pbc-constructible-noetherian-finite-selection).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A stalk-detecting family of maps from a constructible abelian etale sheaf on a
Noetherian scheme has a finite subfamily whose map to the direct sum is monomorphic.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, order 1604; Stacks Tag 09Z6,
partition argument (blueprint: lem-weil-pbc-constructible-noetherian-finite-selection).

Proof: By `lem-weil-pbc-irreducible-lisse-strata`, choose finitely many irreducible
locally closed strata on which the source is locally constant with finite stalks.
At a geometric generic point of each stratum, select one detecting index for each
nonzero element of its finite stalk. The resulting finite-sum map is injective at
that generic point. By `lem-weil-pbc-lisse-generic-kernel`, it is monomorphic on the
whole stratum. Take the union of the finite sets of selected indices over the strata.
Projection to each stratum's selected summands shows injectivity at every geometric
stalk. By `prop-weil-pbc-geometric-stalks-exact`, the kernel has zero geometric stalks;
`lemma-weil-pbc-geometric-stalk-conservative` then makes the kernel zero, hence the map
monomorphic. No finiteness condition is imposed on the target sheaves. -/
theorem exists_mono_biproduct_of_constructible_stalk_detection
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ l : L, F ⟶ G l)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (v : (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)), v ≠ 0 →
        ∃ l : L, (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map (φ l)) v ≠ 0) :
    ∃ L₀ : Finset L, Mono (biproduct.lift (fun l : L₀ => φ l.val)) := by
  sorry

/-- In particular, it suffices that at every geometric point one member of the family
is injective on the whole stalk. Source: smooth purity blueprint, `sk-prop-sf-cbc`,
order 1604; Stacks Tag 09Z6, partition argument
(blueprint: lem-weil-pbc-constructible-noetherian-finite-selection).

Proof: An injective stalk map sends each nonzero element to a nonzero element because
it preserves zero. Thus the hypothesis implies the stalk-detection hypothesis of
`exists_mono_biproduct_of_constructible_stalk_detection`; apply that statement and its
stratification, finite selection, and exact/conservative stalk argument. -/
theorem exists_mono_biproduct_of_constructible_stalk_injective
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ l : L, F ⟶ G l)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ l : L, Function.Injective
        (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).map (φ l))) :
    ∃ L₀ : Finset L, Mono (biproduct.lift (fun l : L₀ => φ l.val)) := by
  sorry

end AlgebraicGeometry.Scheme
