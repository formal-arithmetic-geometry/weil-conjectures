/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-!
# Closure of K-flat complexes under countable sums and cones

Source: Stacks Project, Cohomology on Sites, Lemmas 06YR and 07A3
(blueprint: lem-pc-kflat-cone-direct-sum).

## Main statements

- `CochainComplex.isKFlat_coproduct_nat`: a countable direct sum of K-flat complexes is K-flat.
- `CochainComplex.isKFlat_mappingCone`: the cone of a map of K-flat complexes is K-flat.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- (blueprint: lem-pc-kflat-cone-direct-sum) Stacks, Cohomology on Sites, Lemma 06YR:
the countable direct sum of K-flat complexes of sheaves of `R`-modules is K-flat.

Proof: for every acyclic `F`, total tensor commutes with the coproduct. This coproduct is
acyclic since countable coproducts of sheaves of modules are exact: express it as the filtered
colimit of finite sums and use exactness of filtered colimits. Every tensor summand is acyclic
by K-flatness, so the total tensor of the coproduct is acyclic. -/
theorem isKFlat_coproduct_nat
    (K : ℕ → CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hK : ∀ n : ℕ, (K n).IsKFlat) : (∐ K).IsKFlat := by
  sorry

/-- (blueprint: lem-pc-kflat-cone-direct-sum) Stacks, Cohomology on Sites, Lemma 07A3:
the mapping cone of a morphism of K-flat complexes of sheaves of `R`-modules is K-flat.

Proof: tensoring an acyclic complex with the cone triangle gives the cone triangle of the
tensored morphism. The first two tensor complexes are acyclic by K-flatness; the
tensor-triangle two-out-of-three property makes the third acyclic as well. -/
theorem isKFlat_mappingCone
    {K₁ K₂ : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : K₁ ⟶ K₂) (h₁ : K₁.IsKFlat) (h₂ : K₂.IsKFlat) :
    (mappingCone f).IsKFlat := by
  sorry

end CochainComplex
