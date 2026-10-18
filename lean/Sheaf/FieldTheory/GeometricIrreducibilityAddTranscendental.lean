/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Sheaf.FieldTheory.GeometricIrreducibilityTranscendental

/-!
# Adding a transcendental variable preserves geometric irreducibility

Source: Stacks Project, Algebra, Tag 0G32 (lemma-geometrically-irreducible-add-transcendental)
(blueprint: lem-zl-geometric-irreducibility-add-transcendental).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- If `L/M` is geometrically irreducible and `x` is transcendental over `L`, then adjoining
`x` to both fields preserves geometric irreducibility.

Source: Stacks Project, Algebra, Tag 0G32 (lemma-geometrically-irreducible-add-transcendental)
(blueprint: lem-zl-geometric-irreducibility-add-transcendental).

Proof:
1. Apply the one-variable specialization of
   `lem-zl-geometric-irreducibility-transcendental` to the geometrically irreducible extension
   `L/M` and the one-element algebraically independent family consisting of `x`.
2. Transcendence of `x` over `L` is exactly algebraic independence of this singleton, and the
   resulting generated fields are `L(x)` and `M(x)`, represented below by their canonical
   intermediate fields in `K` over `M`.
-/
theorem geometricallyIrreducible_adjoin_transcendental
    {M : Type u} {L : Type u} {K : Type v}
    [Field M] [Field L] [Field K]
    [Algebra M L] [Algebra L K] [Algebra M K]
    [IsScalarTower M L K]
    (hLM : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap M L))))
    (x : K) (hx : Transcendental L x) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom
        (IntermediateField.inclusion
          (E := IntermediateField.adjoin M ({x} : Set K))
          (F := (IntermediateField.adjoin L ({x} : Set K)).restrictScalars M)
          (IntermediateField.adjoin_le_iff.mpr (fun y hy => by
            simp only [Set.mem_singleton_iff] at hy
            subst y
            change x ∈ IntermediateField.adjoin L ({x} : Set K)
            apply IntermediateField.subset_adjoin
            simp))).toRingHom)) := by
  sorry

end AlgebraicGeometry
