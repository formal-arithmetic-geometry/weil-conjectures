/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple

/-! # Borel subgroup schemes

Source: Milne, Algebraic Groups (2017), Definition 17.6, printed p.353.
(blueprint: def-sfb-borel-subgroup-scheme)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A Borel subgroup is a maximal smooth connected solvable closed subgroup.
Inclusion is factorization of the closed subgroup embeddings; maximality says that
every larger smooth connected solvable closed subgroup factors back through this one.
Solvability uses the scheme-theoretic derived series, not just rational points.
Source: Milne, Definition 17.6, printed p.353.
(blueprint: def-sfb-borel-subgroup-scheme) -/
def IsBorelGroupScheme {F : Type u} [Field F] [IsAlgClosed F]
    {G B : Over (Spec (.of F))} [GrpObj G] [GrpObj B]
    (i : B ⟶ G) : Prop :=
  IsClosedSubgroupScheme i ∧ Smooth B.hom ∧ ConnectedSpace B.left ∧
    IsSolvableGroupScheme B ∧
    ∀ (D : Over (Spec (.of F))) [GrpObj D] (j : D ⟶ G),
      IsClosedSubgroupScheme j → Smooth D.hom → ConnectedSpace D.left →
      IsSolvableGroupScheme D →
      (∃ f : B ⟶ D, f ≫ j = i) → ∃ r : D ⟶ B, r ≫ i = j

end AlgebraicGeometry
