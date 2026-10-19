module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete

/-!
# Coefficient-field section for a separable residue field

Source: `literature/stacks-project/more-algebra.tex`, Tag 0C34,
`lemma-lift-residue-field`, statement and proof
(blueprint: lem-trf-separable-residue-coefficient-section).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/--
For a complete local `k`-algebra whose residue field is separable algebraic over `k`,
there is a `k`-algebra section of the residue map.  The proof follows Stacks Tag
0C34 in two steps: (1) apply the separable-algebraic square-zero lifting theorem
to the zero ideal of the residue field; since every power of that ideal is zero,
this is `def-weil-pbc-formally-smooth-adic` for the zero-adic topology, using
`lem-exc-separable-algebraic-square-zero-lifting`; (2) apply
`lem-weil-pbc-fs-adic-lift-into-complete`, the adic
formal-smooth lifting theorem with source ring `k`, source algebra the residue
field, source ideal zero, target algebra `R`, and both target ideals equal to the
maximal ideal.  Completeness, the power containment and closedness are then
immediate, while the identity residue map sends the zero source ideal to zero;
the resulting lift is the required section.

Source: `literature/stacks-project/more-algebra.tex`, Tag 0C34,
`lemma-lift-residue-field`, statement and proof
(blueprint: lem-trf-separable-residue-coefficient-section).
-/
theorem exists_separable_residueField_section
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Algebra.IsSeparable k (IsLocalRing.ResidueField R)] :
    ∃ σ : IsLocalRing.ResidueField R →ₐ[k] R,
      (IsLocalRing.residue R).comp σ.toRingHom =
        RingHom.id (IsLocalRing.ResidueField R) := by
  sorry

end Algebra
