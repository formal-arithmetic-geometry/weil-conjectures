/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Flat sheaves on an essentially small site

Let `C` be an essentially small site and `A` a Grothendieck abelian category with a symmetric
monoidal closed structure. This file collects, in the form used by the proof of bounded below
proper base change, the structure of the category `Sheaf J A` of `A`-valued sheaves:

- `CategoryTheory.GrothendieckTopology.sheaf_tensor_closed`: `Sheaf J A` is Grothendieck
  abelian, sheafification is exact and strong symmetric monoidal for the sheafified objectwise
  tensor product, and this monoidal structure is symmetric and closed.

The neighbouring blueprint nodes are existing declarations: blueprint `lem-weil-pbc-flat-coproduct`
is `CategoryTheory.ObjectProperty.flat_coproduct`, blueprint
`lem-weil-pbc-sheaf-flat-separator` is
`CategoryTheory.GrothendieckTopology.exists_flat_separator_sheaf_of_essentiallySmall`, and
blueprint `lem-weil-pbc-free-sheaf-flat` is `CategoryTheory.GrothendieckTopology.free_sheaf_flat`
(the sheafified free presheaf `Sheaf.freeYoneda J X P` with flat coefficients is flat; on the
small étale site with `A` the category of `Λ`-modules it is the extension by zero `j_{X!} Λ_X`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- **`A`-valued sheaves on an essentially small site are Grothendieck abelian and symmetric
monoidal closed under the sheafified tensor product.** For a Grothendieck abelian category `A`
with a symmetric monoidal closed structure whose tensor product is additive:

1. `Sheaf J A` is a Grothendieck abelian category, and sheafification is exact;
2. the sheafified objectwise tensor product `F ⊗ G = a(ι F ⊗ ι G)`
   (`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`) is a
   monoidal structure, additive in each variable, for which sheafification `a` is strong
   monoidal (`a(P ⊗ Q) ≅ a P ⊗ a Q`) and braided; it is symmetric
   (`CategoryTheory.Sheaf.symmetricCategory`);
3. this monoidal structure is closed
   (`CategoryTheory.GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall`), so tensoring
   with a fixed sheaf is a left adjoint.

This is blueprint `lem-weil-pbc-sheaf-tensor-closed`. -/
@[stacks 0GMW]
theorem sheaf_tensor_closed :
    IsGrothendieckAbelian.{u + 1} (Sheaf J A) ∧
      PreservesFiniteLimits (presheafToSheaf J A) ∧
      PreservesColimits (presheafToSheaf J A) ∧
      MonoidalPreadditive (Sheaf J A) ∧
      Nonempty (presheafToSheaf J A).Monoidal ∧
      Nonempty (SymmetricCategory (Sheaf J A)) ∧
      Nonempty (MonoidalClosed (Sheaf J A)) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, ⟨inferInstance⟩,
    ⟨Sheaf.symmetricCategory J A⟩, ⟨inferInstance⟩⟩

end CategoryTheory.GrothendieckTopology
