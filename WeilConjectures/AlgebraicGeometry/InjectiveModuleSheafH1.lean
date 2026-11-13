/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.InjectiveEtaleModuleCechH1
import WeilConjectures.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Degree-one abelian cohomology of injective module sheaves

## References

* Stacks Project, Lemma 03FD.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An injective module sheaf has zero degree-one cohomology after forgetting scalars.
(Stacks, Tag 03FD.) -/
theorem subsingleton_H_one_of_injective_module_sheaf
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj J) 1) := by
  let F := (sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J
  let T : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  have hT : Limits.IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply Sheaf.subsingleton_H_one_of_surjective F hT
  intro E Q ι π w hS
  let S := ShortComplex.mk ι π w
  apply Scheme.surjective_sections_of_cech_h1_vanishing Y S hS T
    (fun I V f ↦ Sieve.ofArrows V f ∈ Y.smallEtaleTopology T)
  · intro I V f hf
    exact hf
  · intro I V f hf
    refine ⟨I, V, f, hf, ?_⟩
    intro i
    exact ⟨i, 𝟙 (V i), Category.id_comp _⟩
  · intro I V f hf
    exact Scheme.isZero_cech_H_one_of_injective_module_sheaf Y Λ J T V f hf

end AlgebraicGeometry.Etale
