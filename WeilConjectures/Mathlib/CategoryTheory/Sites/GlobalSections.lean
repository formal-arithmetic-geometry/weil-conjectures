/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
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

end CategoryTheory
