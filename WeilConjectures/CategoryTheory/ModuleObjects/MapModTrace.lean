/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!
# Traces of monoidal adjunctions on module objects

Let `adj : F ⊣ G` be a monoidal adjunction between preadditive monoidal categories, with unit
`u : 𝟭 ⟶ F ⋙ G` a monomorphism at every object. Let `ρ i : F ⋙ G ⟶ F ⋙ G` be finitely many
*monoidal* natural transformations fixing the unit (`u ≫ ρ i = u`), and `t : F ⋙ G ⟶ 𝟭` a natural
transformation factoring their sum through the unit: `t ≫ u = ∑ i, ρ i`. In the application `F ⊣ G`
is `g^* ⊣ g_*` for a finite étale Galois covering `g` with group `Γ`, the `ρ i` are the action of
`Γ` and `t` is the trace.

Then `t` and the `ρ i` are linear over every algebra object `R`, for the module structure of
`G (F M)` through the unit `R ⟶ G (F R)`: they lift to natural transformations of the functor
`F.mapMod R ⋙ G.mapMod (F R) ⋙ Mod.comap (u R)` on `R`-module objects
(`CategoryTheory.Adjunction.mapModTrace`, `CategoryTheory.Adjunction.mapModAction`), with the same
identities with respect to the unit of the lifted adjunction `Adjunction.mapModAdjunction`.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory MonObj Functor.LaxMonoidal

namespace CategoryTheory.Adjunction

open scoped Obj

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  {D : Type*} [Category D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (R : C) [MonObj R]

variable {adj} {ι : Type*} {ρ : ι → (F ⋙ G ⟶ F ⋙ G)} [∀ i, NatTrans.IsMonoidal (ρ i)]
  (hρ : ∀ i, adj.unit ≫ ρ i = adj.unit)

variable [Fintype ι] {t : F ⋙ G ⟶ 𝟭 C} (ht : t ≫ adj.unit = ∑ i, ρ i)
  [∀ X, Mono (adj.unit.app X)]

end CategoryTheory.Adjunction
