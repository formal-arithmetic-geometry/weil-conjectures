module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Finite affine covers with overlap and triple refinements

Source: Stacks Project, Limits, Tag 01ZR, first proof, Zariski gluing preparation;
Schemes, Tags 01IT and 01KO (blueprint: def-trf-finite-affine-refinement-collection).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Finite labels and specified incidences for the affine refinements used in Zariski gluing.
The three components of `subordinate a b c t` select the pair charts containing triple
chart `t`. All roles use one finite label set; labels may denote equal opens.
Source: Stacks, Tag 01ZR, first proof
(blueprint: def-trf-finite-affine-refinement-collection). -/
structure FiniteAffineRefinementShape where
  size : ℕ
  main : Finset (Fin size)
  pair : Fin size → Fin size → Finset (Fin size)
  overlap : Fin size → Fin size → Finset (Fin size)
  triple : Fin size → Fin size → Fin size → Finset (Fin size)
  subordinate : Fin size → Fin size → Fin size → Fin size → Fin size × Fin size × Fin size
  incidence : Finset (Fin size × Fin size)

/-- The affine and covering conditions for a finite labelled collection. Empty finsets
cover precisely empty opens. `incidence` records any further specified inclusions.
Source: Stacks, Tag 01ZR, first proof; Schemes, Tags 01IT and 01KO
(blueprint: def-trf-finite-affine-refinement-collection). -/
structure FiniteAffineRefinementShape.Valid (K : FiniteAffineRefinementShape)
    {X : Scheme.{u}} (C : Fin K.size → X.Opens) : Prop where
  affine : ∀ d, IsAffineOpen (C d)
  main_cover : (⨆ a ∈ K.main, C a) = ⊤
  pair_cover : ∀ a ∈ K.main, ∀ b ∈ K.main,
    (⨆ r ∈ K.pair a b, C r) = C a ⊓ C b
  overlap_cover : ∀ a ∈ K.main, ∀ b ∈ K.main,
    ∀ r ∈ K.pair a b, ∀ s ∈ K.pair a b,
      (⨆ t ∈ K.overlap r s, C t) = C r ⊓ C s
  triple_cover : ∀ a ∈ K.main, ∀ b ∈ K.main, ∀ c ∈ K.main,
    (⨆ t ∈ K.triple a b c, C t) = C a ⊓ C b ⊓ C c
  triple_subordinate : ∀ a ∈ K.main, ∀ b ∈ K.main, ∀ c ∈ K.main,
    ∀ t ∈ K.triple a b c,
      (K.subordinate a b c t).1 ∈ K.pair a b ∧
      (K.subordinate a b c t).2.1 ∈ K.pair a c ∧
      (K.subordinate a b c t).2.2 ∈ K.pair b c ∧
      C t ≤ C (K.subordinate a b c t).1 ∧
      C t ≤ C (K.subordinate a b c t).2.1 ∧
      C t ≤ C (K.subordinate a b c t).2.2
  inclusions : ∀ z ∈ K.incidence, C z.1 ≤ C z.2

end AlgebraicGeometry
