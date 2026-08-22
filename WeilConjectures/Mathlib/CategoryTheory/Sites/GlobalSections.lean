/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The global sections functor is lax monoidal

For a site `(C, J)` and a monoidal category `A` such that `Sheaf J A` carries the
localized monoidal category structure `Sheaf.monoidalCategory`, the global sections
functor `Sheaf.Γ J A : Sheaf J A ⥤ A` is lax monoidal: it is the right adjoint of the
constant sheaf functor, which is monoidal (see
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`), hence in particular oplax
monoidal, so its right adjoint is lax monoidal by `Adjunction.rightAdjointLaxMonoidal`.
We also record the corresponding `Adjunction.IsMonoidal` instance on `constantSheafΓAdj`,
which makes the mate-compatibility lemmas of `Mathlib.CategoryTheory.Monoidal.Functor`
available for this adjunction.

When `A` is moreover braided and `Sheaf J A` carries the braided structure
`Sheaf.braidedCategory`, the global sections functor is lax braided, since the constant
sheaf functor is braided. Since a symmetric monoidal functor is by definition a braided
functor between symmetric monoidal categories, this also covers the symmetric case: for
symmetric `A`, the global sections functor is lax symmetric monoidal.

Finally, we record the projection formula for global sections: since the constant sheaf
functor is strong monoidal, the projection morphism of the constant-sheaf/global-sections
adjunction is an isomorphism at every dualizable coefficient object
(`CategoryTheory.Adjunction.isIso_projectionMap`), giving a natural isomorphism
`Γ(F) ⊗ M ≅ Γ(F ⊗ M̲)` for `M` with a left dual (`CategoryTheory.Sheaf.ΓProjectionIso`).
-/

@[expose] public section

universe v₁ v₃ u₁ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal] [HasGlobalSectionsFunctor J A]

attribute [local instance] Sheaf.monoidalCategory

/-- The global sections functor is lax monoidal, being the right adjoint of the (strong)
monoidal constant sheaf functor. -/
noncomputable instance Sheaf.ΓLaxMonoidal : (Sheaf.Γ J A).LaxMonoidal :=
  (constantSheafΓAdj J A).rightAdjointLaxMonoidal

instance constantSheafΓAdjIsMonoidal : (constantSheafΓAdj J A).IsMonoidal :=
  inferInstance

section BraidedCategory

variable [BraidedCategory A]

attribute [local instance] Sheaf.braidedCategory

/-- The global sections functor is lax braided, being the right adjoint of the braided
constant sheaf functor. Since a symmetric monoidal functor is by definition a braided
functor between symmetric monoidal categories, for symmetric `A` this says that the
global sections functor is lax symmetric monoidal. -/
noncomputable instance Sheaf.ΓLaxBraided : (Sheaf.Γ J A).LaxBraided :=
  (constantSheafΓAdj J A).rightAdjointLaxBraided

end BraidedCategory

section ProjectionFormula

open MonoidalCategory

variable {J A}

/-- The projection morphism of the constant-sheaf/global-sections adjunction is an
isomorphism at coefficients admitting a left dual. This is an instance of
`CategoryTheory.Adjunction.isIso_projectionMap`; we record it so that it is found
directly at the `constantSheafΓAdj` head symbol. -/
instance isIso_projectionMap_constantSheafΓAdj (F : Sheaf J A) (M : A) [HasLeftDual M] :
    IsIso ((constantSheafΓAdj J A).projectionMap F M) :=
  inferInstance

/-- The projection formula for global sections: for a dualizable object `M` of the
coefficient category, the projection morphism of the constant-sheaf/global-sections
adjunction gives an isomorphism `Γ(F) ⊗ M ≅ Γ(F ⊗ M̲)`, where `M̲` denotes the constant
sheaf at `M`. It is natural in the sheaf `F` by
`CategoryTheory.Adjunction.projectionMap_natural_left`. -/
noncomputable def Sheaf.ΓProjectionIso (F : Sheaf J A) (M : A) [HasLeftDual M] :
    (Γ J A).obj F ⊗ M ≅ (Γ J A).obj (F ⊗ (constantSheaf J A).obj M) :=
  asIso ((constantSheafΓAdj J A).projectionMap F M)

@[simp]
lemma Sheaf.ΓProjectionIso_hom (F : Sheaf J A) (M : A) [HasLeftDual M] :
    (ΓProjectionIso F M).hom = (constantSheafΓAdj J A).projectionMap F M :=
  rfl

end ProjectionFormula

end CategoryTheory
