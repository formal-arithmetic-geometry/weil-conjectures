/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Transfer of functorial injective embeddings along an adjunction

Source: Stacks Project, Homology, Lemma 0161
(blueprint: lem-exc-rg-adjoint-transfer-functorial-injectives).
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

/--
Source: Stacks Homology Lemma 0161 (blueprint: lem-exc-rg-adjoint-transfer-functorial-injectives).

Given an adjunction whose left adjoint is faithful and preserves monomorphisms,
transfer the functorial injective embeddings of `M` to `D` as follows.

1. Set the replacement functor to `v ⋙ J ⋙ u`. At `B`, compose the unit with
   `u.map (j.app (v.obj B))`. Naturality follows from that of `j` and the unit.
2. Each `J.obj (v.obj B)` is injective. The right adjoint `u` sends it to an
   injective object because `v` preserves monomorphisms (Stacks Lemma 015Z;
   blueprint node lem-exc-rg-right-adjoint-preserves-injectives).
3. Each transferred component is mono: after applying `v`, compose with the
   counit. Naturality of the counit and the triangle identity reduce this to
   `j.app (v.obj B)`. Cancel that mono, then use faithfulness of `v`.
4. The functor, natural transformation, mono components and injective values
   give the required functorial injective embeddings on `D`.
-/
theorem adjunction_transfer_functorial_injective_embeddings
    {D : Type u₁} [Category.{v₁} D] {M : Type u₂} [Category.{v₂} M]
    (v : D ⥤ M) (u : M ⥤ D) (adj : v ⊣ u)
    [v.PreservesMonomorphisms] [v.Faithful]
    (J : M ⥤ M) (j : 𝟭 M ⟶ J)
    (hjmono : ∀ X : M, Mono (j.app X))
    (hjinj : ∀ X : M, Injective (J.obj X)) :
    ∃ (jD : 𝟭 D ⟶ v ⋙ J ⋙ u),
      (∀ B : D, jD.app B = adj.unit.app B ≫ u.map (j.app (v.obj B))) ∧
        (∀ B : D, Mono (jD.app B)) ∧
          (∀ B : D, Injective ((v ⋙ J ⋙ u).obj B)) := by
  sorry

end CategoryTheory
