/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction to a dense subsite preserves and reflects `W`

Let `H : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)`, and let `A` be a
concrete category such that both `J.W` and `K.W` (the classes of morphisms of
presheaves which become isomorphisms after sheafification) agree with the classes
of locally bijective morphisms. We show that a morphism `f` of presheaves on `D`
satisfies `K.W` if and only if its restriction `whiskerLeft H.op f` to `C`
satisfies `J.W` (`CategoryTheory.GrothendieckTopology.W_whiskerLeft_iff_of_isDenseSubsite`).
Equivalently, `K.W` is the inverse image of `J.W` under the restriction functor
(`CategoryTheory.GrothendieckTopology.W_inverseImage_whiskeringLeft_of_isDenseSubsite`).

Mathlib's `CategoryTheory.GrothendieckTopology.W_whiskerLeft_iff` (in
`Mathlib.CategoryTheory.Sites.Equivalence`) proves the analogous statement for a
cover-dense *full* functor whose sheaf pushforward is essentially surjective; the
version here instead applies to arbitrary dense subsites (which are only locally
full), at the price of requiring concrete coefficients with
`WEqualsLocallyBijective` on both sides.
-/

@[expose] public section

universe w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.GrothendieckTopology

open Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (H : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [H.IsDenseSubsite J K]
  {A : Type u₃} [Category.{v₃} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]
  [hJ : J.WEqualsLocallyBijective A] [hK : K.WEqualsLocallyBijective A]

include hJ hK

/-- If `H : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, then a morphism
of presheaves on `D` becomes an isomorphism after sheafification if and only if its
restriction to `C` does. -/
lemma W_whiskerLeft_iff_of_isDenseSubsite {P Q : Dᵒᵖ ⥤ A} (f : P ⟶ Q) :
    J.W (whiskerLeft H.op f) ↔ K.W f := by
  have := IsDenseSubsite.isCoverDense J K H
  rw [J.W_iff_isLocallyBijective, K.W_iff_isLocallyBijective,
    Presheaf.isLocallyInjective_whisker_iff J K H f (IsDenseSubsite.coverPreserving J K H),
    Presheaf.isLocallySurjective_whisker_iff J K H f (IsDenseSubsite.coverPreserving J K H)]

variable (A) in
/-- If `H : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, then `K.W` is
the inverse image of `J.W` under the restriction functor. -/
lemma W_inverseImage_whiskeringLeft_of_isDenseSubsite :
    (J.W (A := A)).inverseImage ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj H.op) = K.W (A := A) := by
  ext P Q f
  exact W_whiskerLeft_iff_of_isDenseSubsite H J K f

end CategoryTheory.GrothendieckTopology
