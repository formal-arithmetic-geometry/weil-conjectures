/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Compact objects of an additive category with coproducts

Source: the blueprint of the Weil conjectures, chapter `sec-picard-framework`, unit
`sk-thm-picard-duality` (blueprint: def-pc-compact-object); Stacks Project, Derived Categories,
Definition 13.37.1 (Tag 09SM).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits DirectSum

namespace CategoryTheory

open Classical in
/-- (blueprint: def-pc-compact-object) Let `C` be an additive category with arbitrary coproducts.
An object `K` of `C` is *compact* if, for every set `I` and family `E : I → C`, the canonical map
`⨁ᵢ Hom(K, E i) → Hom(K, ⨁ᵢ E i)`, sending `f` in the `i`-th summand to `f ≫ Sigma.ι E i`, is
bijective (Stacks, Tag 09SM). The direct sum is taken with the classical decidable equality
on `I`. -/
def IsCompactObject {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (K : C) :
    Prop :=
  ∀ (I : Type w) (E : I → C),
    Function.Bijective
      (DirectSum.toAddMonoid (fun i : I => Preadditive.rightComp K (Sigma.ι E i)) :
        (⨁ i : I, (K ⟶ E i)) →+ (K ⟶ ∐ E))

end CategoryTheory
