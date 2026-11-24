/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Descent of separatedness along a surjective universally closed morphism

## References

* Stacks Project, Morphisms, Lemma 09MQ, part (4).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Separatedness over a scheme descends along a surjective universally closed morphism.
(Stacks, Tag 09MQ) -/
theorem isSeparated_of_surjective_universallyClosed {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ q = p)
    [Surjective f] [UniversallyClosed f] [IsSeparated p] : IsSeparated q := by
  let F := Limits.pullback.map p p q q f f (𝟙 S)
    ((Category.comp_id p).trans h.symm) ((Category.comp_id p).trans h.symm)
  have : UniversallyClosed F :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed)
      (inferInstance : UniversallyClosed f) (inferInstance : UniversallyClosed f) h.symm h.symm
  have hdiag : Limits.pullback.diagonal p ≫ F = f ≫ Limits.pullback.diagonal q := by
    apply Limits.pullback.hom_ext <;> simp [F]
  have hclosed : IsClosed (Set.range (f ≫ Limits.pullback.diagonal q)) := by
    rw [← hdiag]
    exact (Scheme.Hom.isClosedMap (Limits.pullback.diagonal p ≫ F)).isClosed_range
  have hrange : Set.range (f ≫ Limits.pullback.diagonal q) =
      Set.range (Limits.pullback.diagonal q) := by
    change Set.range ((Limits.pullback.diagonal q) ∘ f) = _
    exact (Surjective.surj (f := f)).range_comp _
  constructor
  exact IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hclosed)

end AlgebraicGeometry
