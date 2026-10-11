/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The injectivity criterion using subobjects of a generator

Source: Stacks Project, Injectives, Lemma 19.11.6 (Tag 079G)
(blueprint: lem-pur-kinjective-characterize-injective).
-/

universe v u

namespace CategoryTheory

/-- Stacks Project, Lemma 19.11.6 (Tag 079G)
(blueprint: lem-pur-kinjective-characterize-injective).
An object is injective precisely when every map from a subobject of a generator extends to
that generator.

Proof: In the forward direction, apply the extension property of an injective object to the
monomorphism `M.arrow` (def-sp-injective-resolutions). Conversely, fix a monomorphism
`A ↪ B` and a map `φ : A ⟶ I`. Order the pairs consisting of a subobject `A ⊆ A' ⊆ B`
and an extension `φ' : A' ⟶ I` by inclusion and compatibility. A nonempty chain has an
upper bound given by its filtered colimit: exactness of filtered colimits makes the induced
map into `B` monic (def-sp-grothendieck-abelian). The empty chain has the original pair
`(A, φ)` as an upper bound. Zorn's lemma gives a maximal pair `(A', φ')`.

If `A'` is proper in `B`, the generator property detects the nonzero quotient map `B ⟶ B/A'`:
there is `ψ : U ⟶ B` not factoring through `A'` (def-sp-grothendieck-abelian). Set
`N = A' ∩ Im(ψ)` and `M = ψ⁻¹(N)`. The induced map `M ⟶ N` is epic. The hypothesis
extends the composite `M ⟶ N ⟶ A' ⟶ I` to `χ : U ⟶ I`. Since `Ker(ψ) ⊆ M` and the
restriction of `χ` factors through `N`, it vanishes on `Ker(ψ)`. Thus `χ` descends to
`φ'' : Im(ψ) ⟶ I`. The epimorphism `M ⟶ N` shows that `φ''` and `φ'` agree on `N`.
Glue them along `N` to a map `A' + Im(ψ) ⟶ I`. This extends `φ'` on a strictly larger
subobject, contradicting maximality. Hence `A' = B`, and the resulting map extends `φ`.
Since the original monomorphism and map were arbitrary, `I` is injective
(def-sp-injective-resolutions). -/
theorem injective_iff_extends_subobject_generator {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] (U I : C) (hU : IsSeparator U) :
    Injective I ↔ ∀ (M : Subobject U) (f : (M : C) ⟶ I),
      ∃ g : U ⟶ I, M.arrow ≫ g = f := by
  sorry

end CategoryTheory
