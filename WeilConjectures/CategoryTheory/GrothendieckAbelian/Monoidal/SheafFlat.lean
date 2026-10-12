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
  tensor product, and this monoidal structure is symmetric and closed;
- `CategoryTheory.GrothendieckTopology.flat_freeYoneda`: the sheafified free presheaf
  `P_X^# = Sheaf.freeYoneda J X P` on an object `X` of `C`, with flat coefficients `P`, is
  flat. On the small étale site with `A` the category of `Λ`-modules, `Sheaf.freeYoneda J X Λ`
  is the extension by zero `j_{X!} Λ_X` of the constant sheaf.
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

omit [MonoidalPreadditive A] in
/-- **The sheafified free presheaf on an object with flat coefficients is flat.** For an object
`X` of `C` and a flat object `P` of `A`, the sheaf `P_X^# = Sheaf.freeYoneda J X P` associated
to the presheaf `V ↦ ∐_{V ⟶ X} P` is flat: each value of the presheaf is a coproduct of copies
of `P`, hence flat (`CategoryTheory.ObjectProperty.flat_coproduct`), and the sheafification of a
presheaf with flat values is flat
(`CategoryTheory.GrothendieckTopology.flat_presheafToSheaf_obj`).
This is blueprint `lem-weil-pbc-free-sheaf-flat`. -/
@[stacks 03EV]
theorem flat_freeYoneda (X : C) {P : A} (hP : ObjectProperty.flat P) :
    ObjectProperty.flat (Sheaf.freeYoneda J X P) := by
  refine flat_presheafToSheaf_obj A J _ fun V ↦ ?_
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} A
    (ULift.{u + 1} (V.unop ⟶ X))
  exact ObjectProperty.prop_of_iso _
    (Sigma.whiskerEquiv (f := fun _ : ULift.{u + 1} (V.unop ⟶ X) ↦ P) Equiv.ulift
      fun _ ↦ Iso.refl P)
    (ObjectProperty.flat_coproduct _ fun _ ↦ hP)

end CategoryTheory.GrothendieckTopology
