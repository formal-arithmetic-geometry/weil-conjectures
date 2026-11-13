/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Locally quasi-finite morphisms are locally of finite type

## References

* [Stacks, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally quasi-finite morphism in the Stacks sense is locally of finite type.
(Stacks, Tags 01TD, 01T2) -/
theorem locallyOfFiniteType_of_isLocallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : f.IsLocallyQuasiFinite) : LocallyOfFiniteType f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hx, hU, V, hV, e, hft, _⟩ := hf x
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, hft⟩

end AlgebraicGeometry.Scheme.Hom
