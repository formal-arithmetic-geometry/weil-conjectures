/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Counits, transposes and composition under adjoint-equivalence conjugation

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-purity-transport/prop-pur-adic-reconstruction-trace-coherence.proof.md,
sole paragraph, abstract counit transport and coherence calculations; Stacks 0037 and 0DV0
(blueprint: lem-pur-adjoint-equivalence-conjugation-calculus).

An equivalence `E : C ≌ N` packages the specified `R ⊣ L`, with `R = E.functor`,
`L = E.inverse`, unit `E.unitIso.hom` and counit `E.counitIso.hom`.
Conversely, `Adjunction.toEquivalence` packages any adjunction with invertible unit and
counit without changing those maps. The reverse adjunction is `E.symm.toAdjunction`:
its unit is `E.counitIso.inv` and its counit is `E.unitIso.inv`.

The conjugate of `F` is `E₁.functor ⋙ F ⋙ E₂.inverse`; the conjugate of `α` is
`Functor.whiskerRight (Functor.whiskerLeft E₁.functor α) E₂.inverse`.
The comparison `c_F` is the existing natural isomorphism
`E₁.invFunIdAssoc (F ⋙ E₂.inverse)`. Its components are `L₂(F(e₁))` by
`Equivalence.invFunIdAssoc_hom_app`. Thus its naturality in object maps and its
invertibility are part of its type, including for `G` with the two equivalences exchanged.
The compositor is `Functor.isoWhiskerLeft (E₁.functor ⋙ F) (E₂.invFunIdAssoc (H ⋙ E₃.inverse))`;
its components are `L₃(H(e₂))`, by the same existing component formula.

## Main statements

- `conjugation_counit`: counit of the specified composite adjunction.
- `conjugation_transpose`: transpose of the transported map.
- `conjugation_comparison_naturality`: comparison naturality in functor transformations.
- `conjugation_compositor_naturality`: compositor naturality in both transformations.
-/

@[expose] public section

universe u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃ z₁ z₂ z₃

namespace CategoryTheory.AdjointEquivalenceConjugation

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  {N₁ : Type w₁} {N₂ : Type w₂} {N₃ : Type w₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Category.{z₁} N₁] [Category.{z₂} N₂] [Category.{z₃} N₃]

end CategoryTheory.AdjointEquivalenceConjugation
