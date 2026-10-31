/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda

/-! # Comparing a represented support Hom functor with a restricted right adjoint -/

@[expose] public noncomputable section
set_option autoImplicit false
universe v w u t
open CategoryTheory
namespace CategoryTheory

/-- A representing object in a full subcategory is the value of any specified
right adjoint on that subcategory, compatibly with the representing counit.
Source: blueprint finite Verdier coefficient normalization and finite-field pullback,
representing-Hom identification in paragraph (i).
(blueprint: lem-sf-constructible-adjoint-representing-object).

Proof: turn the representing counit into a morphism in the target full subcategory
and transpose it by the given adjunction. Precomposition with its transpose agrees,
by naturality of the adjunction, with the assumed representing-Hom bijection.
Yoneda therefore makes the transpose an isomorphism. Applying the full-subcategory
inclusion gives the asserted ambient isomorphism. The inverse adjunction Hom
equivalence identifies its counit composite with epsilon. This uses every object of the
source full subcategory, including the proposed representing object itself, and
requires no ambient representability outside that subcategory. -/
theorem adjointValueOfRepresentingObject
    {C : Type u} {B : Type t} [Category.{v} C] [Category.{w} B]
    (P : ObjectProperty C) (Q : ObjectProperty B) (R : C ⥤ B)
    (hp : ∀ K : P.FullSubcategory, Q (R.obj K.obj))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ R) hp ⊣ G)
    (N : Q.FullSubcategory) (W : C) (hW : P W)
    (ε : R.obj W ⟶ N.obj)
    (hrep : ∀ K : P.FullSubcategory,
      Function.Bijective (fun f : K.obj ⟶ W ↦ R.map f ≫ ε)) :
    ∃ i : W ≅ (G.obj N).obj,
      R.map i.hom ≫ (adj.counit.app N).hom = ε := by
  let W₀ : P.FullSubcategory := ⟨W, hW⟩
  let ε₀ : (Q.lift (P.ι ⋙ R) hp).obj W₀ ⟶ N := ⟨ε⟩
  let θ : W₀ ⟶ G.obj N := adj.homEquiv W₀ N ε₀
  have hθ : IsIso θ := by
    apply isIso_of_yoneda_map_bijective θ
    intro K
    let j : (K ⟶ W₀) ≃ (K.obj ⟶ W) :=
      ⟨fun f ↦ f.hom, fun f ↦ ⟨f⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
    let s : (R.obj K.obj ⟶ N.obj) ≃ ((Q.lift (P.ι ⋙ R) hp).obj K ⟶ N) :=
      ⟨fun f ↦ ⟨f⟩, fun f ↦ f.hom, fun _ ↦ rfl, fun _ ↦ rfl⟩
    let e := j.trans ((Equiv.ofBijective _ (hrep K)).trans
      (s.trans (adj.homEquiv K N)))
    convert e.bijective using 1
    funext f
    change f ≫ adj.homEquiv W₀ N ε₀ =
      adj.homEquiv K N ⟨R.map f.hom ≫ ε⟩
    rw [← Adjunction.homEquiv_naturality_left]
    rfl
  refine ⟨P.ι.mapIso (asIso θ), ?_⟩
  have h := (adj.homEquiv W₀ N).symm_apply_apply ε₀
  rw [Adjunction.homEquiv_counit] at h
  exact congrArg (fun f : (Q.lift (P.ι ⋙ R) hp).obj W₀ ⟶ N ↦ f.hom) h

end CategoryTheory
