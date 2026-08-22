/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Functor
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

When both `A` and `Sheaf J A` are monoidal closed, we also record the companion formula
for internal homs: global sections of the sheaf hom out of a constant sheaf are the
internal hom of the coefficients into global sections, `Γ [M̲, F] ≅ [M, Γ F]`
(`CategoryTheory.Sheaf.ΓIhomIso`, natural in `F` by `CategoryTheory.Sheaf.ΓIhomNatIso`).
This is the instantiation at `constantSheafΓAdj` of the internal hom adjunction formula
`CategoryTheory.Adjunction.ihomNatIso`; in contrast to the projection formula, no
dualizability hypothesis on `M` is needed.
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

section IhomFormula

open MonoidalCategory Functor.LaxMonoidal

variable {A} [MonoidalClosed A] [MonoidalClosed (Sheaf J A)]

/-- Global sections of the sheaf hom out of a constant sheaf are the internal hom of
the coefficients into global sections: the natural isomorphism
`Γ [M̲, −] ≅ [M, Γ −]` of functors `Sheaf J A ⥤ A`, where `M̲` denotes the constant
sheaf at `M`. This is the internal hom adjunction formula
`CategoryTheory.Adjunction.ihomNatIso` at the constant-sheaf/global-sections
adjunction; no dualizability hypothesis on `M` is needed. -/
noncomputable def Sheaf.ΓIhomNatIso (M : A) :
    ihom ((constantSheaf J A).obj M) ⋙ Γ J A ≅ Γ J A ⋙ ihom M :=
  (constantSheafΓAdj J A).ihomNatIso M

variable {J}

/-- Global sections of the sheaf hom out of a constant sheaf are the internal hom of
the coefficients into global sections: `Γ [M̲, F] ≅ [M, Γ F]`, where `M̲` denotes the
constant sheaf at `M`. It is natural in `F` by `CategoryTheory.Sheaf.ΓIhomNatIso`. -/
noncomputable def Sheaf.ΓIhomIso (M : A) (F : Sheaf J A) :
    (Γ J A).obj ((ihom ((constantSheaf J A).obj M)).obj F) ≅
      (ihom M).obj ((Γ J A).obj F) :=
  (constantSheafΓAdj J A).ihomIso M F

/-- The forward map of `CategoryTheory.Sheaf.ΓIhomIso` is, after uncurrying, the
composite of the unit of the constant-sheaf/global-sections adjunction, the lax monoidal
structure of the global sections functor and the evaluation of the sheaf hom. -/
lemma Sheaf.uncurry_ΓIhomIso_hom (M : A) (F : Sheaf J A) :
    MonoidalClosed.uncurry (ΓIhomIso M F).hom =
      (constantSheafΓAdj J A).unit.app M ▷
          (Γ J A).obj ((ihom ((constantSheaf J A).obj M)).obj F) ≫
        μ (Γ J A) ((constantSheaf J A).obj M)
          ((ihom ((constantSheaf J A).obj M)).obj F) ≫
        (Γ J A).map ((ihom.ev ((constantSheaf J A).obj M)).app F) :=
  (constantSheafΓAdj J A).uncurry_ihomIso_hom M F

end IhomFormula

end CategoryTheory
