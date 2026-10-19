/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleAlgebraClosure

/-!
# Geometric irreducibility passes to field subextensions

Source: Stacks Project, Algebra, Tag 037N (lemma-subalgebra-geometrically-irreducible),
part (1) (blueprint: lem-zl-geometric-irreducibility-subextension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `k ⊆ L ⊆ K` is a tower of fields and `Spec K` is geometrically irreducible over `k`,
then `Spec L` is geometrically irreducible over `k`.

Source: Stacks Project, Algebra, Tag 037N, assertion (1), specialized to fields
(blueprint: lem-zl-geometric-irreducibility-subextension).

Proof: The field tower gives `k`-algebra structures on `L` and `K`, and the canonical
map `IsScalarTower.toAlgHom k L K` is injective because it is the algebra map between
fields. Apply `geometricallyIrreducible_spec_of_injective` to this map and the assumed
geometric irreducibility of `Spec K` over `k`. -/
theorem geometricallyIrreducible_spec_of_field_subextension
    (k L K : Type u) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K]
    (hK : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  exact geometricallyIrreducible_spec_of_injective (IsScalarTower.toAlgHom k L K)
    (algebraMap L K).injective hK

end AlgebraicGeometry
