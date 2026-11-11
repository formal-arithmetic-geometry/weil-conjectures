/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility

/-!
# Lisse complexes

Let `Λ` be a commutative condensed ring and `X` a scheme. A `Λ_X`-module is lisse if it has
a finite constant local model on a pro-étale cover of `X` itself
(`ProEtale.HasFiniteConstantLocalModel`, blueprint `definition-lisse-sheaves--1`). A complex
`K ∈ D(X_proét, Λ)` is lisse if all its cohomology sheaves are lisse
(`ProEtale.IsLisseComplex`, blueprint `definition-lisse-sheaves--2`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A complex `K ∈ D(X_proét, Λ)` is *lisse* if its cohomology sheaves `Hⁿ(K)` are lisse
`Λ_X`-modules, i.e. each has a finite constant local model on a pro-étale cover of `X`.
No boundedness is imposed.
(blueprint: definition-lisse-sheaves--2) -/
def IsLisseComplex (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : Prop :=
  ∀ n : ℤ, HasFiniteConstantLocalModel Λ X ((DerivedCategory.homologyFunctor _ n).obj K)

end AlgebraicGeometry.ProEtale
