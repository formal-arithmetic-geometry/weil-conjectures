/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

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

/-- (blueprint: lem-pc-kflat-cone-direct-sum) Stacks, Cohomology on Sites, Lemma 07A3:
the mapping cone of a morphism of K-flat complexes of sheaves of `R`-modules is K-flat.

Proof: tensoring an acyclic complex with the cone triangle gives the cone triangle of the
tensored morphism. The first two tensor complexes are acyclic by K-flatness; the
tensor-triangle two-out-of-three property makes the third acyclic as well. -/
theorem isKFlat_mappingCone
    {K₁ K₂ : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : K₁ ⟶ K₂) (h₁ : K₁.IsKFlatTensor) (h₂ : K₂.IsKFlatTensor) :
    (mappingCone f).IsKFlatTensor := by
  let := SheafOfModules.monoidalCategory R
  intro A hA
  exact (SheafOfModules.tensor_mappingCone_two_out_of_three R A K₁ K₂ f hA
    |>.2.1) ⟨h₁ A hA, h₂ A hA⟩

end CochainComplex
