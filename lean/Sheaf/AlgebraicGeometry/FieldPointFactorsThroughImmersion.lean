/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Field-valued points factor through immersions

Source: literature/stacks-project/schemes.tex, Definitions 01IO and 01HK,
Lemmas 01HI, 0356, and 01L7, and the discussion before Lemma 01J9
(blueprint: lem-weil-pbc-field-point-factors-through-immersion).
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An immersion induces residue-field isomorphisms and uniquely lifts field-valued
points whose image is the image of a chosen point. First factor the immersion as a
closed immersion followed by an open immersion and compare the two residue-field maps
using `lem-weil-pbc-residue-field-point-naturality` and
`lem-weil-pbc-closed-immersion-residue-field-iso`; their composite is an isomorphism.
For a field-valued point, lift uniquely through the open factor by
`lem-weil-pbc-morphism-factors-through-open-subscheme`, then through the closed factor
by `lem-weil-pbc-field-point-factors-through-closed-immersion`. Uniqueness follows from
`lem-weil-pbc-open-immersion-monomorphism` and the closed-factor uniqueness. The final
universal quantification includes the algebraically closed-field case defining geometric
points.
Source: Stacks Project, Schemes, Definitions 01IO and 01HK, Lemmas 01HI, 0356,
and 01L7, and the discussion before Lemma 01J9
(blueprint: lem-weil-pbc-field-point-factors-through-immersion). -/
theorem fieldPoint_factorsThrough_immersion
    {Z X : Scheme.{u}} (iota : Z ⟶ X) [IsImmersion iota]
    (z : Z) :
    IsIso (iota.residueFieldMap z) ∧
      ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ X),
        s.base ((default : Spec (.of K))) = iota.base z →
          (∃! s' : Spec (.of K) ⟶ Z, s' ≫ iota = s) ∧
            ∀ s' : Spec (.of K) ⟶ Z,
              s' ≫ iota = s → s'.base ((default : Spec (.of K))) = z := by
  sorry

end AlgebraicGeometry
