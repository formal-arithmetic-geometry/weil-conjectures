/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The reduction is a universal homeomorphism

## References

* [Stacks Project, Tag 054M](https://stacks.math.columbia.edu/tag/054M)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01J4](https://stacks.math.columbia.edu/tag/01J4)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The reduction is reduced and its canonical map is a surjective closed immersion
and a universal homeomorphism. The proof follows Stacks Lemma 054M and Lemma 01J3. -/
theorem reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism
    (X : Scheme.{u}) :
    IsReduced X.nilradical.subscheme ∧
      IsClosedImmersion X.nilradical.subschemeι ∧
        Surjective X.nilradical.subschemeι ∧
          (topologically IsHomeomorph).universally X.nilradical.subschemeι := by
  have hsurj : Surjective X.nilradical.subschemeι := by
    constructor
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  refine ⟨inferInstance, inferInstance, hsurj, ?_⟩
  intro X' Y' i₁ i₂ f' h
  have : IsClosedImmersion f' :=
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
      h.flip (inferInstance : IsClosedImmersion X.nilradical.subschemeι)
  have : Surjective f' :=
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback h.flip hsurj
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f'.isEmbedding, f'.surjective⟩

end AlgebraicGeometry
