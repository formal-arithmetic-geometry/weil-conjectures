/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Exact adjunctions with fully faithful left adjoint and zero kernel

Source: Stacks Project, derived.tex, Tag 09J1,
lemma-fully-faithful-adjoint-kernel-zero
(blueprint: lem-sfb-exact-adjoint-zero-kernel-equivalence).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- The unit and counit of an exact adjunction are natural isomorphisms if the left
adjoint is fully faithful and the right adjoint detects zero objects.

Source: Stacks Project, derived.tex, Tag 09J1,
lemma-fully-faithful-adjoint-kernel-zero
(blueprint: lem-sfb-exact-adjoint-zero-kernel-equivalence).

Proof: By lem-sp-adjunction-unit-fully-faithful-left (Stacks 07RB), full
faithfulness of F makes the unit invertible. For Y in D, the right triangle
identity says that the unit at G(Y), followed by G of the counit at Y, is the
identity, so G of that counit is invertible. Complete the counit F(G(Y)) → Y
to a distinguished triangle with cone Z, using TR1 from
def-weil-triangulated-category. Exactness of G gives its distinguished image
triangle. By lem-kun-distinguished-cone-zero (Stacks 05QR), its third object
G(Z) is zero. The zero-kernel hypothesis then makes Z zero. The same cone
criterion in D makes the counit at Y invertible. Naturality of the counit
implies naturality of its componentwise inverses, so the counit is a natural
isomorphism. Together with the unit this exhibits F and G as inverse equivalences. -/
theorem isIso_unit_and_counit_of_fully_faithful_of_zero_kernel
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] [F.Full] [F.Faithful]
    (adj : F ⊣ G) (hG : ∀ Y : D, IsZero (G.obj Y) → IsZero Y) :
    IsIso adj.unit ∧ IsIso adj.counit := by
  sorry

end CategoryTheory.Adjunction
