/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-! # The six-factor tensor exchange product

The explicit composite used in the proper external product comparison, with all functors
retained as arguments before the exchange transformation is evaluated.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- Compose the symmetry, first projection, mapped symmetry, exchange tensor identity,
second projection and direct-image comparison, in that order.
Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/
sk-thm-sf-kunneth-relative.proof.md, Coherence (i), final sentence.
(blueprint: def-sf-tensor-exchange-product-map).

Construction: take the given six arrows and compose them in order. The intermediate
objects are respectively `Rg L ⊗ Rf M`, `Rg (L ⊗ Fg (Rf M))`,
`Rg (Fg (Rf M) ⊗ L)`, `Rg (Rq (Fp M) ⊗ L)`,
`Rg (Rq (Fp M ⊗ Fq L))` and `Rt (Fp M ⊗ Fq L)`.
No inverse or choice is used. -/
def tensorExchangeProductMap
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    [mC : MonoidalCategory C] [mD : MonoidalCategory D] [mE : MonoidalCategory E]
    {Rf : H ⥤ C} {Fg : C ⥤ D} {Fp : H ⥤ E}
    {Rq : E ⥤ D} {Rg : D ⥤ C} {Fq : D ⥤ E} {Rt : E ⥤ C}
    (τ : Rf ⋙ Fg ⟶ Fp ⋙ Rq) (d : Rq ⋙ Rg ⟶ Rt) (M : H) (L : D)
    (s₀ : Rf.obj M ⊗ Rg.obj L ⟶ Rg.obj L ⊗ Rf.obj M)
    (πg : Rg.obj L ⊗ Rf.obj M ⟶ Rg.obj (L ⊗ Fg.obj (Rf.obj M)))
    (s₁ : L ⊗ Fg.obj (Rf.obj M) ⟶ Fg.obj (Rf.obj M) ⊗ L)
    (πq : Rq.obj (Fp.obj M) ⊗ L ⟶ Rq.obj (Fp.obj M ⊗ Fq.obj L)) :
    Rf.obj M ⊗ Rg.obj L ⟶ Rt.obj (Fp.obj M ⊗ Fq.obj L) :=
  s₀ ≫ πg ≫ Rg.map s₁ ≫ Rg.map (τ.app M ⊗ₘ 𝟙 L) ≫ Rg.map πq ≫ d.app _

end CategoryTheory
