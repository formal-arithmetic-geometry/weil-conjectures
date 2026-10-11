/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# K-flatness and flatness under the telescope construction

Source: Stacks Project, Cohomology on Sites, proof of Lemma 06YS, with Lemmas 06YQ,
06YR and 07A3; Modules on Sites, Lemma 03EU (blueprint: lem-pc-kflat-closure).

The site and module universes are those of the landed `SheafOfModules.IsFlat`
(`C : Type u`, `Category.{u} C`, rings and modules in `u`).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Bounded-above flat complexes are K-flat; K-flat complexes are closed under mapping
cones, countable direct sums and sequential homotopy colimits; countable sums of flat
sheaves of modules are flat.
Source: Stacks Project, proof of Tag 06YS, Tags 06YQ, 06YR, 07A3 and 03EU
(blueprint: lem-pc-kflat-closure).

Proof:
1. Apply `lem-pc-bounded-above-flat-kflat-site`: truncate an acyclic test complex above,
tensor with the bounded-above flat complex, and filter the total complex. The graded
pieces are acyclic by flatness. Pass to the filtered colimit using exactness.
2. Apply `lem-pc-kflat-cone-direct-sum`: total tensor commutes with cones and countable
sums, and both constructions preserve acyclicity. For a sequence, its homotopy colimit
is the cone of `1 - shift` on its sum (`lem-pc-complex-hocolim-colimit`), so it is K-flat.
3. The sheaf-module category is Grothendieck abelian
(`prop-pur-kinjective-resolutions-exist`) and its tensor is symmetric monoidal closed
(`lem-pc-sheaf-modules-tensor-closed`). Tensor with a flat sheaf preserves finite limits.
Apply `lem-weil-pbc-flat-coproduct`; right exactness and symmetry then give exactness of
tensor-right with the sum, hence flatness by `def-pc-flat-sheaf-modules`. -/
theorem kFlat_closure
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) :
    (∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) → K.IsKFlat) ∧
    (∀ (K L : CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : K ⟶ L),
      K.IsKFlat → L.IsKFlat → (mappingCone f).IsKFlat) ∧
    (∀ (I : Type u) [Countable I],
      ∀ K : I → CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      (∀ i : I, (K i).IsKFlat) → (∐ K).IsKFlat) ∧
    (∀ (K : ℕ → CochainComplex (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
        (t : ∀ n : ℕ, K n ⟶ K (n + 1)),
      (∀ n : ℕ, (K n).IsKFlat) →
      (mappingCone (𝟙 (∐ K) -
        Sigma.desc (fun n : ℕ => t n ≫ Sigma.ι K (n + 1)))).IsKFlat) ∧
    (∀ (I : Type u) [Countable I],
      ∀ F : I → SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      (∀ i : I, SheafOfModules.IsFlat (F i)) → SheafOfModules.IsFlat (∐ F)) := by
  sorry

end CochainComplex
