/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction

/-! # Closed symmetric monoidal dualizability criterion

Source: Stacks Project, Cohomology, Tag 0FPC
(blueprint: lem-pc-dualizable-evaluation-criterion).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/- The evaluation isomorphism criterion for a dualizable object in `D(O_X)`.
The bijection `adj` is a tensor--internal-Hom bijection of
`lem-sc-derived-internal-hom-adjunction`, with the naturality equation of
`scheme_derivedInternalHom_adjunction` as hypothesis `hadj`.
Source: Stacks Project, Cohomology, Tag 0FPC
(blueprint: lem-pc-dualizable-evaluation-criterion).

Proof:
1. Naturality of the adjunction in its first variable: for `f : A → B` and
   `g : B ⊗ K → M` with adjunct `g♭ : B → RHom(K,M)`, the adjunct of `(f ⊗ 1_K) ≫ g`
   is `f ≫ g♭`. Take `A = O_X`, `B = K ⊗ D`, `f = η`, `g = 1_K ⊗ e`, whose adjunct is
   `φ_K`. The adjunct of `(η ⊗ 1_K) ≫ (1_K ⊗ e)` is `η ≫ φ_K`, the adjunct of `id_K` by
   the definition of `η`; bijectivity gives the first triangle identity.
2. Put `g := (1_D ⊗ η) ≫ (e ⊗ 1_D) : D → D`. The map `φ_{O_X} : D = O_X ⊗ D → RHom(K,O_X)`
   is the adjunct of `e` and an isomorphism. By naturality, `g ≫ φ_{O_X}` is the adjunct of
   `(g ⊗ 1_K) ≫ e`. Bifunctoriality (`e ⊗ e` computed two ways) and Step 1 give
   `(g ⊗ 1_K) ≫ e = e`, so `g ≫ φ_{O_X} = φ_{O_X}` and `g = id_D` since `φ_{O_X}` is an
   isomorphism. Associators and unitors are inserted throughout. -/

end AlgebraicGeometry
