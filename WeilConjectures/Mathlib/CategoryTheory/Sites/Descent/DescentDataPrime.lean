/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data from gluing morphisms

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, `f i : X i ⟶ S` a family of
morphisms with chosen pullbacks `sq` and chosen threefold pullbacks `sq₃`. Given morphisms
`μ i : X i ⟶ W i`, objects `O i` over `W i` and *gluing morphisms*
`H i j : ((sq i j).p₁ ≫ μ i)^* (O i) ⟶ ((sq i j).p₂ ≫ μ j)^* (O j)` satisfying the identity and
cocycle conditions, we obtain a descent datum `DescentData'.ofGlue` for the objects
`(μ i)^* (O i)`.

We then compare an object `M` over `S` effectively descending such a descent datum with an object
`N` over another base `S'` mapping to `S`, along a family `f' i : X' i ⟶ S'` over the `f i`:
if the pullbacks of the gluing morphisms are induced by isomorphisms
`ε i : (m i)^* (O i) ≅ (f' i)^* N`, then `h^* M ≅ N`
(`DescentData'.nonempty_map_iso_of_ofGlue`), provided that `F.toDescentData f'` is fully
faithful.

This is used to glue modules of finite presentation descended to a finite stage of a cofiltered
limit of schemes.
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Limits

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

end LocallyDiscreteOpToCat

open LocallyDiscreteOpToCat

namespace DescentData'

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
  {W : ι → C} (μ : ∀ i, X i ⟶ W i) (O : ∀ i, F.obj (.mk (op (W i))))
  (H : ∀ i j, (F.map ((sq i j).p₁ ≫ μ i).op.toLoc).toFunctor.obj (O i) ⟶
    (F.map ((sq i j).p₂ ≫ μ j).op.toLoc).toFunctor.obj (O j))

variable {d : ∀ i, X i ⟶ (sq i i).pullback} {hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _}
  {hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _}

variable {sq₃ μ O H}

end DescentData'

namespace DescentData'

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
  {W : ι → C} {μ : ∀ i, X i ⟶ W i} {O : ∀ i, F.obj (.mk (op (W i)))}
  {H : ∀ i j, (F.map ((sq i j).p₁ ≫ μ i).op.toLoc).toFunctor.obj (O i) ⟶
    (F.map ((sq i j).p₂ ≫ μ j).op.toLoc).toFunctor.obj (O j)}
  {d : ∀ i, X i ⟶ (sq i i).pullback} {hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _}
  {hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _}

section IsoGlueHom

variable (sq) {N : F.obj (.mk (op S))}
  (ε : ∀ i, (F.map (μ i).op.toLoc).toFunctor.obj (O i) ≅ (F.map (f i).op.toLoc).toFunctor.obj N)

variable {sq}

end IsoGlueHom

section Pull

variable {S' : C} {X' : ι → C} {f' : ∀ i, X' i ⟶ S'} {sq' : ∀ i j, ChosenPullback (f' i) (f' j)}
  {r : ∀ i, X' i ⟶ X i} (r₂ : ∀ i j, (sq' i j).pullback ⟶ (sq i j).pullback)
  (hr₂₁ : ∀ i j, r₂ i j ≫ (sq i j).p₁ = (sq' i j).p₁ ≫ r i)
  (hr₂₂ : ∀ i j, r₂ i j ≫ (sq i j).p₂ = (sq' i j).p₂ ≫ r j)
  {μ' : ∀ i, X' i ⟶ W i} (hμ : ∀ i, r i ≫ μ i = μ' i)

variable (sq₃) {sq₃' : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq' i₁ i₂) (sq' i₂ i₃) (sq' i₁ i₃)}
  (r₃ : ∀ i₁ i₂ i₃, (sq₃' i₁ i₂ i₃).pullback ⟶ (sq₃ i₁ i₂ i₃).pullback)
  (h₁₂ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₁₂ = (sq₃' i₁ i₂ i₃).p₁₂ ≫ r₂ i₁ i₂)
  (h₂₃ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₂₃ = (sq₃' i₁ i₂ i₃).p₂₃ ≫ r₂ i₂ i₃)
  (h₁₃ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₁₃ = (sq₃' i₁ i₂ i₃).p₁₃ ≫ r₂ i₁ i₃)
  (hr₃₁ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₁ = (sq₃' i₁ i₂ i₃).p₁ ≫ r i₁)
  (hr₃₂ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₂ = (sq₃' i₁ i₂ i₃).p₂ ≫ r i₂)
  (hr₃₃ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₃ = (sq₃' i₁ i₂ i₃).p₃ ≫ r i₃)

end Pull

end DescentData'

end CategoryTheory.Pseudofunctor
