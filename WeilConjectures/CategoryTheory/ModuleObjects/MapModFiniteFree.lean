/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!
# Transport of finite free module objects along an additive lax monoidal functor

Let `P : C ⥤ D` be an additive lax monoidal functor between abelian monoidal categories and `R`
an algebra object of `C`. Transport of module objects along `P` sends the regular module `R` to
the regular module `P R` (`CategoryTheory.Functor.mapModRegularIso`), hence the finite free
module `Rᵈ` to the finite free module `(P R)ᵈ` (`CategoryTheory.Functor.mapModFiniteFreeIso`).
Consequently, if `S` is finite free of rank `d` as an `R`-module through `φ : R ⟶ S`, then so
is `P S` as a `P R`-module through `P φ` (`CategoryTheory.Functor.comapRegularIsoFiniteFree`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Functor

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (P : C ⥤ D) [P.LaxMonoidal] (R : C) [MonObj R]

/-- Transport along a lax monoidal functor `P` sends the regular module `R` to the regular
module `P R`. -/
def mapModRegularIso : (P.mapMod R).obj (Mod.regular R) ≅ Mod.regular (P.obj R) :=
  Mod.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp])

variable [Abelian C] [Abelian D] [MonoidalPreadditive C] [MonoidalPreadditive D] [P.Additive]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft (P.obj R))]

/-- Transport along an additive lax monoidal functor `P` sends the finite free module `Rᵈ` to
the finite free module `(P R)ᵈ`. -/
noncomputable def mapModFiniteFreeIso (d : ℕ) :
    (P.mapMod R).obj (Mod.finiteFree R d) ≅ Mod.finiteFree (P.obj R) d :=
  (P.mapMod R).mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ P.mapModRegularIso R

variable {R} {S : C} [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- If `S` is finite free of rank `d` as an `R`-module through `φ : R ⟶ S`, then `P S` is
finite free of rank `d` as a `P R`-module through `P φ`, for an additive lax monoidal functor
`P`. -/
noncomputable def comapRegularIsoFiniteFree {d : ℕ}
    (e : (Mod.comap φ).obj (Mod.regular S) ≅ Mod.finiteFree R d) :
    (Mod.comap (P.map φ)).obj (Mod.regular (P.obj S)) ≅ Mod.finiteFree (P.obj R) d :=
  (Mod.comap (P.map φ)).mapIso (P.mapModRegularIso S).symm ≪≫
    ((P.mapModComapIso φ).app (Mod.regular S)).symm ≪≫ (P.mapMod R).mapIso e ≪≫
    P.mapModFiniteFreeIso R d

end CategoryTheory.Functor
