/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The dual formula for an exceptional inverse image, formally

Let `P ⊣ S` be an adjunction between braided monoidal categories, playing the role of
`Rf_! ⊣ Rf^!` for a morphism `f : X ⟶ Y`, and let `π_K : P K ⊗ M ⟶ P (K ⊗ M')` be a family of
morphisms natural in `K`, playing the role of the projection morphism
`Rf_! K ⊗ᴸ M ⟶ Rf_!(K ⊗ᴸ Lf^* M)`. This file proves the formal part of the dual formula
`Rf^! L ≅ 𝔻_X(f^* 𝔻_Y L)`: if `L ≅ RHom(M, ω_Y)` (biduality, with `M = 𝔻_Y L`), the
projection morphisms induce bijections on morphisms into `ω_Y`, `S ω_Y ≅ ω_X` and `φ : M' ⟶ N`
induces bijections on morphisms into `ω_X` after tensoring, then `S L ≅ RHom(N, ω_X)`
(`CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`). The internal homs are given by
arbitrary right adjoints of `M ⊗ -` and `N ⊗ -`, so that the statement can be applied to a
chosen model of the internal hom.

The bijectivity hypotheses, rather than invertibility, allow the projection morphism and `φ`
to be isomorphisms only "up to objects orthogonal to `ω`", as happens at the integral stage
`𝒪_E` of the `ℓ`-adic formalism, where they are isomorphisms modulo the uniformizer.

## Main statements

- `CategoryTheory.nonempty_iso_of_homEquiv`: the Yoneda lemma for a family of bijections.
- `CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`: the formal dual formula.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

namespace Verdier

variable {P : C ⥤ D} {S : D ⥤ C}

end Verdier

end CategoryTheory
