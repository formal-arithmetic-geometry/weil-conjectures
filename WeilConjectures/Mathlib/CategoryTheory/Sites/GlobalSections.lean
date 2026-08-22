/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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

Finally, when the monoidal structure on `Sheaf J A` is closed, the global sections of
the internal hom compute the hom-sets of sheaves: morphisms from the monoidal unit of
`A` into `Γ [F, G]` are the sheaf morphisms `F ⟶ G`
(`CategoryTheory.Sheaf.unitHomΓIhomEquiv`), by combining the global-sections adjunction,
the unit comparison of the monoidal constant sheaf functor and the internal-hom
adjunction.
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

section MonoidalClosed

open MonoidalCategory MonoidalClosed

variable [MonoidalClosed (Sheaf J A)]

/-- Morphisms from the monoidal unit of `A` into the global sections of the internal
sheaf hom `[F, G]` are the sheaf morphisms `F ⟶ G`: the composite of the global-sections
adjunction, the unit comparison isomorphism of the monoidal constant sheaf functor, the
internal-hom adjunction and the right unitor. -/
noncomputable def Sheaf.unitHomΓIhomEquiv (F G : Sheaf J A) :
    (𝟙_ A ⟶ (Γ J A).obj ((ihom F).obj G)) ≃ (F ⟶ G) where
  toFun h := (ρ_ F).inv ≫ MonoidalClosed.uncurry
    (Functor.LaxMonoidal.ε (constantSheaf J A) ≫
      ((constantSheafΓAdj J A).homEquiv (𝟙_ A) ((ihom F).obj G)).symm h)
  invFun u := (constantSheafΓAdj J A).homEquiv (𝟙_ A) ((ihom F).obj G)
    ((Functor.Monoidal.εIso (constantSheaf J A)).inv ≫
      MonoidalClosed.curry ((ρ_ F).hom ≫ u))
  left_inv h := by
    simp [MonoidalClosed.curry_uncurry]
  right_inv u := by
    simp [MonoidalClosed.uncurry_curry]

/-- Naturality of `Sheaf.unitHomΓIhomEquiv` in the target sheaf, in the style of
`Adjunction.homEquiv_naturality_right`. -/
lemma Sheaf.unitHomΓIhomEquiv_naturality_right (F : Sheaf J A) {G G' : Sheaf J A}
    (h : 𝟙_ A ⟶ (Γ J A).obj ((ihom F).obj G)) (g : G ⟶ G') :
    unitHomΓIhomEquiv J A F G' (h ≫ (Γ J A).map ((ihom F).map g)) =
      unitHomΓIhomEquiv J A F G h ≫ g := by
  dsimp only [unitHomΓIhomEquiv, Equiv.coe_fn_mk]
  rw [Adjunction.homEquiv_naturality_right_symm,
    ← Category.assoc (Functor.LaxMonoidal.ε (constantSheaf J A)),
    MonoidalClosed.uncurry_natural_right]
  simp only [Category.assoc]

/-- Naturality of `Sheaf.unitHomΓIhomEquiv` in the target sheaf, in the style of
`Adjunction.homEquiv_naturality_right_symm`. -/
lemma Sheaf.unitHomΓIhomEquiv_symm_naturality_right (F : Sheaf J A) {G G' : Sheaf J A}
    (u : F ⟶ G) (g : G ⟶ G') :
    (unitHomΓIhomEquiv J A F G').symm (u ≫ g) =
      (unitHomΓIhomEquiv J A F G).symm u ≫ (Γ J A).map ((ihom F).map g) := by
  rw [Equiv.symm_apply_eq, unitHomΓIhomEquiv_naturality_right, Equiv.apply_symm_apply]

end MonoidalClosed

end CategoryTheory
