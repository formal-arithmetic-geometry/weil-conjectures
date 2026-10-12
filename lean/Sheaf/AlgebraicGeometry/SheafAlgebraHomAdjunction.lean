/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule

/-! # The underived algebra-valued sheaf Hom adjunction

Source: Stacks Project, Modules, Tag 0A6F; Duality for Schemes, Tags 0BV0 and 0BV1
(blueprint: lem-sc-sheaf-algebra-hom-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Restriction of scalars is left adjoint to the explicitly constructed algebra-valued Hom.

Proof: For a B-module sheaf M and an O-module sheaf F, send a morphism φ from the
scalar restriction of M to F to ψ with ψ_U(m)_V(b) = φ_V(b • res_{U,V}(m)).
Here V ranges over opens contained in U, as in `sheafAlgebraHomSections`.
Conversely send ψ to φ_U(m) = (ψ_U(m)).app (op (Over.mk (𝟙 U))) 1.
Additivity in m and b follows from distributivity and additivity of φ. O-linearity
in b follows from O-linearity of φ and the scalar-tower identity. B-linearity in m
follows from associativity and commutativity of multiplication and
`sheafAlgebraHom_smul`: multiplying ψ by c precomposes its argument by c.
For V contained in U, restrictions preserve products and scalar multiplication;
φ's naturality therefore makes the family in V a presheaf morphism and the family
in U a sheaf morphism into `sheafAlgebraHomObj`. Evaluation at 1 is O-linear by
`sheafAlgebraHom_underlying_linear`, and commutes with restrictions since ring
restriction preserves 1. The composites are φ(1 • m) = φ(m) and
ψ(b • m)(1) = (b • ψ(m))(1) = ψ(m)(b). Thus the two maps are inverse.
Precomposition in M and postcomposition in F commute with these formulas;
`sheafAlgebraHomMap` is precisely postcomposition, so the equivalences are natural
in both variables. Apply `Adjunction.mkOfHomEquiv` to these natural equivalences.
The same formulas work when B is the zero ring or the scheme is empty: units and
module identities still hold, and no choice of a nonzero section was used.

Source: Stacks Project, Modules, Tag 0A6F; Duality for Schemes, Tags 0BV0 and 0BV1
(blueprint: lem-sc-sheaf-algebra-hom-adjunction). -/
theorem sheafAlgebraHom_adjunction (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)) ⊣ sheafAlgebraHom Y B) := by
  sorry

end AlgebraicGeometry
