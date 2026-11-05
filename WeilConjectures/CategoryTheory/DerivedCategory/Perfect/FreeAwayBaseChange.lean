/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Embedding.RestrictionExtend
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FiniteFree

/-!
# Finite free local models which are stable under base change

Let `K` be a perfect complex of flat `A`-modules in degrees `[0, b]`, and `ι : K ⟶ C` a morphism
to a complex `C` indexed by `ℕ` (extended by zero to `ℤ`) which is a quasi-isomorphism after
every base change. For every prime `p` of `A` there are `s ∉ p`, a complex `P` of finite free
`A_s`-modules in degrees `[0, b]` and a morphism `P ⟶ A_s ⊗[A] C` which stays a
quasi-isomorphism after every base change `A_s ⟶ B`
(`CochainComplex.exists_free_away_quasiIso_baseChange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

variable (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A' B]
  [Algebra A B] [IsScalarTower A A' B]

end ModuleCat

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {A : Type u} [CommRing A]

variable [HasDerivedCategory.{u} (ModuleCat.{u} A)]

end CochainComplex
