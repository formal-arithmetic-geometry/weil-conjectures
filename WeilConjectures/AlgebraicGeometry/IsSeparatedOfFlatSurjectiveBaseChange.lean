/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Descent of separatedness along a flat surjective quasi-compact morphism

## References

* Stacks Project, Descent, Lemma Tag 02KU, the descent direction for a one-member fpqc
  covering.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separatedness descends along a flat surjective quasi-compact base change.
(Stacks, Tags 02KU, 03L7) -/
theorem isSeparated_of_flat_surjective_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]
    [IsSeparated (pullback.snd f g)] : IsSeparated f := by
  have hbase : (MorphismProperty.diagonal @UniversallyClosed) (pullback.snd f g) := by
    rw [MorphismProperty.diagonal_iff]
    infer_instance
  have hdiag : (MorphismProperty.diagonal @UniversallyClosed) f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hbase
  have : UniversallyClosed (pullback.diagonal f) :=
    MorphismProperty.diagonal_iff.mp hdiag
  exact ⟨IsClosedImmersion.of_isPreimmersion (pullback.diagonal f)
    (pullback.diagonal f).isClosedMap.isClosed_range⟩

end AlgebraicGeometry
