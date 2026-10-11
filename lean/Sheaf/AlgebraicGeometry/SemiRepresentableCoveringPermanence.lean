/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.SemiRepresentableObject

/-!
# Permanence of coverings of semi-representable étale objects

Source: Stacks Project, Tag 01G4, Lemma 25.3.2
(blueprint: lem-weil-pbc-semi-representable-covering-permanence).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Coverings of semi-representable objects are stable under composition and base change.
Source: Stacks Project, Tag 01G4, Lemma 25.3.2
(blueprint: lem-weil-pbc-semi-representable-covering-permanence).

Proof: by def-weil-pbc-semi-representable-object, a covering is a covering family over each
index of its target. For (1), fix an index of M. Compose the family of b-components over
that index with the a-component families using lem-weil-pbc-etale-covering-composition.
The bijection sending i to (a.f i, i) identifies the resulting family with the components
of a ≫ b, so the composite is a covering. For (2),
lem-weil-pbc-semi-representable-finite-limits constructs the pullback using matching pairs
of indices and the componentwise scheme pullbacks in the étale site. Fix an index of L'.
The projections over it are the base changes of the a-components over its image in L.
By lem-weil-pbc-etale-covering-base-change, these are jointly surjective étale maps,
hence a covering family. This proves the projection is a semi-representable covering.
-/
theorem semiRepresentableCovering_comp_baseChange {X : Scheme.{u}}
    {K L : FormalCoproduct.{w} X.Etale} (a : K ⟶ L)
    (ha : IsSemiRepresentableCovering a) :
    (∀ {M : FormalCoproduct.{w} X.Etale} (b : L ⟶ M),
      IsSemiRepresentableCovering b → IsSemiRepresentableCovering (a ≫ b)) ∧
    (∀ {L' : FormalCoproduct.{w} X.Etale} (c : L' ⟶ L),
      IsSemiRepresentableCovering (pullback.fst c a : pullback c a ⟶ L')) := by
  sorry

end AlgebraicGeometry.Scheme
