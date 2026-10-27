module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.AdicCompletion

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
there is a `k`-algebra section of the residue map. By
`Algebra.FormallyEtale.of_isSeparable`, the residue field is formally étale,
and hence formally smooth, over `k`. Apply
`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` to its identity
map into `R` modulo the maximal ideal. Completeness gives a lift to `R` whose
reduction is the identity. Taking underlying ring homomorphisms gives the
required section equation. This is the formally smooth lifting argument of
Stacks Tag 0C34, using Mathlib's complete-target lifting theorem directly.

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
  have : FormallyEtale k (IsLocalRing.ResidueField R) :=
    FormallyEtale.of_isSeparable k (IsLocalRing.ResidueField R)
  obtain ⟨σ, hσ⟩ := FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (I := IsLocalRing.maximalIdeal R) (AlgHom.id k (IsLocalRing.ResidueField R))
  exact ⟨σ, congrArg AlgHom.toRingHom hσ⟩

end Algebra
