/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Lifting maps from bounded projective complexes

Source: Stacks Project, derived.tex, Tag 064E (blueprint: lem-pc-ring-derived-map-lift).
-/

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

namespace RingTheory

/-- (blueprint: lem-pc-ring-derived-map-lift)
Let `R` be a ring and `n : ℤ`.  A bounded complex `P` of projective
`R`-modules which vanishes below `n` lifts maps through a derived morphism
which is an isomorphism above `n` and an epimorphism in degree `n`.
The proof follows the Stacks Project Tag 064E argument.  First complete
`α` to a distinguished triangle by (TR1), represent its cone by a complex,
and use the long exact cohomology sequence (`lem-sf-derived-homology-long-exact`)
to show that the cone has zero cohomology in every degree at least `n`.
Next apply precise vanishing (`lem-pc-ring-precise-vanishing`) to conclude
that the composite from `P` to the cone is zero.  Exactness of Hom into the
triangle (`lem-weil-pbc-hom-into-triangle-exact`) then gives a lift
`δ : Q.obj P ⟶ Q.obj E` of `β`.  Finally, the representative theorem
(`lem-pc-ring-derived-map-representative`) supplies a chain map `γ : P ⟶ E`
with `Q.map γ = δ`, yielding the displayed equality.
-/
theorem derived_map_lift
    (R : Type u) [Ring R]
    (n : ℤ)
    (P E L : CochainComplex (ModuleCat R) ℤ)
    (hbounded : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hprojective : ∀ i : ℤ, Projective (P.X i))
    (hbelow : ∀ i : ℤ, i < n → IsZero (P.X i))
    [HasDerivedCategory.{w} (ModuleCat R)]
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj L)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
    (hα_iso : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α))
    (hα_epi : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) n).map α)) :
    ∃ γ : P ⟶ E, DerivedCategory.Q.map γ ≫ α = β := by
  sorry

end RingTheory
