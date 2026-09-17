/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local surjectivity is checked on a basis

A morphism of presheaves on a topological space is locally surjective as soon as it is
surjective on the sections over every member of a basis of opens: shrinking an open subset to
a basic neighbourhood of a point is exactly the freedom that local surjectivity allows.

This is the criterion that makes local surjectivity usable in practice, where surjectivity on
the sections over *every* open subset is far too strong a demand.

## Main results

- `TopCat.Presheaf.isLocallySurjective_of_isBasis`

-/

@[expose] public section

universe v u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat.{v}}
variable {ℱ 𝒢 : X.Presheaf C}

/-- **A morphism of presheaves surjective on the sections over every member of a basis of opens
is locally surjective.** -/
theorem isLocallySurjective_of_isBasis {B : Set (Opens X)} (hB : Opens.IsBasis B) (T : ℱ ⟶ 𝒢)
    (h : ∀ U ∈ B, Function.Surjective (T.app (op U))) : IsLocallySurjective T := by
  rw [isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  exact ⟨V, hVU, h V hV _, hxV⟩

end TopCat.Presheaf
