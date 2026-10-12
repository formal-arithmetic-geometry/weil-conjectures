module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Sheaf.RingTheory.GlobalDimension

/-! Finite global dimension gives finite projective dimension for the residue field.

Source: Stacks Project, Algebra, Proposition 00OC, implication (2) ⇒ (1).
(blueprint: lem-weil-pbc-residue-field-finite-projective-dimension)
-/

@[expose] public section

universe u v

namespace Ring

/-- The residue field of a ring of finite global dimension has finite projective dimension.
Source: Stacks Project, Algebra, Proposition Tag 00OC, implication (2) ⇒ (1).
(blueprint: lem-weil-pbc-residue-field-finite-projective-dimension). -/
theorem residueField_hasFiniteProjectiveDimension (R : Type u) [CommRing R]
    [IsLocalRing R] (h : Ring.HasFiniteGlobalDimension.{u, max u v} R) :
    ModuleCat.HasFiniteProjectiveDimension
      (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  sorry

end Ring
