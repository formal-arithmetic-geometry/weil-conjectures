/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence

/-!
# Mates of isomorphisms along equivalences

Consider a square of functors

```
      L₁
   C --→ D
 G ↓     ↓ H
   E --→ F
      L₂
```

with adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. In general the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an
isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` need not be an isomorphism. It is one if the vertical functors
`G` and `H` are equivalences: then the iterated mate is the conjugate of the original
isomorphism, hence an isomorphism, and the second mate correspondence, taken along the
adjoint equivalences of `G` and `H`, preserves and reflects isomorphisms.

This is the categorical input showing that the exchange transformations of an automorphism
square of schemes are isomorphisms.

## Main results

- `CategoryTheory.isIso_mateEquiv_of_isEquivalence`.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

set_option linter.flexible false in
/-- **The mate of an isomorphism along equivalences is an isomorphism.** For adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` and equivalences `G` and `H`, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an
isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` is an isomorphism. -/
theorem isIso_mateEquiv_of_isEquivalence (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [G.IsEquivalence]
    [H.IsEquivalence] (α : TwoSquare G L₁ L₂ H) [IsIso α.natTrans] :
    IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  let adj₃ := G.asEquivalence.toAdjunction
  let adj₄ := H.asEquivalence.toAdjunction
  have : IsIso (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)).natTrans := by
    rw [iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α]
    infer_instance
  generalize mateEquiv adj₁ adj₂ α = β at this
  obtain ⟨γ, rfl⟩ : ∃ γ, (mateEquiv adj₄ adj₃).symm γ = β := ⟨_, Equiv.symm_apply_apply _ _⟩
  rw [Equiv.apply_symm_apply] at this
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun X ↦ ?_
  -- The components are composites of components of `γ` with units and counits of the adjoint
  -- equivalences; `simp` reduces the goal to the invertibility of an identity.
  simp [adj₃, adj₄]
  exact IsIso.id _

end CategoryTheory
