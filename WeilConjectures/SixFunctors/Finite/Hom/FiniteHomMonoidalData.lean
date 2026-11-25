/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # The finite-Hom monoidality predicate

The predicate `FiniteHomDomainMonoidal` recording strong monoidality with prescribed
components.

## Implementation details

The predicate is relocated verbatim to let its generic scalar realization compile separately.

## References

- Stacks Project, Tags 07A4, 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a₁ a₂ b₁ b₂
open CategoryTheory MonoidalCategory
namespace WeilConjectures

/-- Strong monoidality of `F` with prescribed tensor, unit and signed symmetry components,
identified with those of a `CoreMonoidal` structure by heterogeneous equalities, such that `F`
commutes with the symmetries. -/
def FiniteHomDomainMonoidal {C : Type a₁} {C' : Type a₂}
    [Category.{b₁} C] [Category.{b₂} C'] [MonoidalCategory C] [MonoidalCategory C']
    (F : C ⥤ C') {V : C → C → Type b₂} (δ : ∀ U V', V U V')
    {W : Type b₂} (e : W)
    {B : C → C → Type b₁} (σ : ∀ U V, B U V)
    {B' : C' → C' → Type b₂} (σ' : ∀ U V, B' U V) : Prop :=
  ∃ S : F.CoreMonoidal,
    HEq S.εIso.symm e ∧
    (∀ U V, HEq (S.μIso U V).symm (δ U V)) ∧
    (∃ β : ∀ U V : C, U ⊗ V ≅ V ⊗ U,
      ∃ β' : ∀ U V : C', U ⊗ V ≅ V ⊗ U,
      (∀ U V, HEq (β U V) (σ U V)) ∧
      (∀ U V, HEq (β' U V) (σ' U V)) ∧
      ∀ U V, (β' (F.obj U) (F.obj V)).hom ≫ (S.μIso V U).hom =
        (S.μIso U V).hom ≫ F.map (β U V).hom)

end WeilConjectures
