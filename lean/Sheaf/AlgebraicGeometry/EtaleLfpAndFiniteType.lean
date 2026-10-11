/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Etale morphisms and finite type over a field

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit
`sk-prop-sf-kunneth-ordinary`, lemma `lem-kun-etale-lfp`
(blueprint: lem-kun-etale-lfp).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An etale morphism is locally of finite presentation. If it is quasi-compact and its
 target is of finite type over a field, its source is of finite type over the same field.
Finite type is written as quasi-compactness and local finite type.

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
lemma `lem-kun-etale-lfp` (blueprint: lem-kun-etale-lfp).

Proof: By `def-weil-pbc-scheme-conventions`, etale includes local finite presentation,
which implies local finite type: finitely presented algebras are finitely generated.
The finite-type structure map of the target is quasi-compact and locally of finite type.
Quasi-compactness is preserved by composition: the inverse image of an affine open is
covered by finitely many affine opens, each having quasi-compact inverse image
(`AlgebraicGeometry.quasiCompact_comp`). Local finite type is preserved by composition:
a finitely generated algebra over a finitely generated algebra is finitely generated
(`AlgebraicGeometry.locallyOfFiniteType_comp`). Thus the composite structure map is
quasi-compact and locally of finite type, hence of finite type over the field. -/
theorem etale_lfp_and_finiteType_over_field {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    LocallyOfFinitePresentation f ∧
      ∀ (K : Type u) [Field K] (g : X ⟶ Spec (CommRingCat.of K)),
        QuasiCompact f → (QuasiCompact g ∧ LocallyOfFiniteType g) →
          QuasiCompact (f ≫ g) ∧ LocallyOfFiniteType (f ≫ g) := by
  sorry

end AlgebraicGeometry
