/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.VerticalWindowComponentNaturality

/-!
# The single-degree smart window as a functor

## References

* Stacks Project, Homology, spectral sequences of double complexes, item (5)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The smart window at a single degree is naturally the homology in that degree,
placed in a single-term complex. -/
theorem verticalWindow_single_iso (q : ℕ) :
    Nonempty (verticalWindow (C := C) (q : ℤ) (q + 1) ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q ⋙
        HomologicalComplex.single C (ComplexShape.up ℕ) q) := by
  let F := verticalWindow (C := C) (q : ℤ) (q + 1)
  let G := HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q ⋙
    HomologicalComplex.single C (ComplexShape.up ℕ) q
  let app : ∀ K : CochainComplex C ℕ, F.obj K ≅ G.obj K := fun K ↦
    verticalWindowComponentIso (C := C) q K
  refine ⟨CategoryTheory.NatIso.ofComponents app ?_⟩
  intro K L f
  simpa [app, F, G, HomologicalComplex.homologyFunctor] using
    verticalWindow_component_naturality (C := C) q f

end HomologicalComplex₂
