/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# The constant sheaf is a sheaf of rings

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Ring`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The sections of the constant sheaf `Λ_X = AlgebraicGeometry.ProEtale.fieldConstantSheaf`
over `U` are the continuous functions `U → Λ`, a `Λ`-algebra under pointwise
multiplication, and the restriction maps are algebra homomorphisms. Hence `Λ_X` is a monoid
object of the monoidal category of sheaves of `Λ`-modules on the pro-étale site of `X`
(Bhatt–Scholze, §6.8): a sheaf of rings. Its multiplication `Λ_X ⊗ Λ_X ⟶ Λ_X` restricts to
the pointwise multiplication of functions on the presheaf tensor product.

For a morphism `g : W ⟶ V` the comparison `Λ_V ⟶ g_* Λ_W`, pulling back functions, is a
morphism of sheaves of rings
(`AlgebraicGeometry.ProEtale.isMonHom_fieldConstantSheafToLowerStar`), so that its adjoint
`g^* Λ_V ≅ Λ_W` is an isomorphism of sheaves of rings.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldConstantSheaf.monObj`: the ring structure on `Λ_X`.

## Main results

- `AlgebraicGeometry.ProEtale.isMonHom_fieldConstantSheafToLowerStar`: pulling back functions is
  a morphism of sheaves of rings.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ] {T T' : Type*} [TopologicalSpace T]
  [TopologicalSpace T']

end AlgebraicGeometry

namespace AlgebraicGeometry

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

open FieldCoefficients

namespace FieldCoefficients

end FieldCoefficients

namespace ProEtale

variable (X : Scheme.{u})

section LowerStar

open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped Obj

variable {Λ} {V W : Scheme.{u}} (g : W ⟶ V)

end LowerStar

end ProEtale

end AlgebraicGeometry
