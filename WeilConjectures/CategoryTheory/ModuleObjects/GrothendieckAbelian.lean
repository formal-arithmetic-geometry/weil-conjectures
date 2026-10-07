/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Braided
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!

# Module objects in a closed symmetric monoidal Grothendieck abelian category

Let `C` be a closed symmetric monoidal Grothendieck abelian category whose tensor product is
additive, and let `R : C` be a commutative algebra object. The category `Mod C R` of
`R`-module objects is abelian (`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`) and
symmetric monoidal for the relative tensor product `⊗_R`
(`WeilConjectures.CategoryTheory.ModuleObjects.Braided`). This file records that `Mod C R`
inherits the remaining properties of `C` needed by the K-flat machinery:

* `Mod.monoidalClosed`: `Mod C R` is closed monoidal;
* `Mod.isGrothendieckAbelian`: `Mod C R` is Grothendieck abelian;
* `Mod.hasFunctorialFlatResolution`: `Mod C R` admits functorial flat resolutions if `C` does.

## Sorried input

All three instances are currently `sorry`ed. The intended arguments are:

* The internal hom `Hom_R(M, N)` is the equalizer of the two maps `[M, N] ⇉ [R ⊗ M, N]`, adjoint
  to `R ⊗ M ⊗ [M, N] ⟶ R ⊗ N ⟶ N` and to `R ⊗ M ⊗ [M, N] ⟶ M ⊗ [M, N] ⟶ N`, with the
  `R`-action induced by that of `N`.
* Colimits and finite limits of module objects are computed in `C` (`R ⊗ -` preserves colimits
  because `C` is closed), so `Mod C R` satisfies AB5, and `R ⊗ G` is a separator for a separator
  `G` of `C`, since `Hom_R(R ⊗ G, M) ≅ Hom(G, M)`.
* If `F` is flat in `C`, then `R ⊗ F` is flat in `Mod C R` because `(R ⊗ F) ⊗_R M ≅ F ⊗ M`; and
  a functorial flat resolution `P(M) ⟶ M` in `C` gives the functorial epimorphism
  `R ⊗ P(M) ⟶ R ⊗ M ⟶ M` of `R`-modules.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The relative tensor product of module objects over a commutative algebra object in a closed
symmetric monoidal Grothendieck abelian category is closed. -/
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  sorry

/-- The category of module objects over a commutative algebra object in a closed symmetric
monoidal Grothendieck abelian category is Grothendieck abelian. -/
instance isGrothendieckAbelian : IsGrothendieckAbelian.{v} (Mod C R) :=
  sorry

/-- If `C` admits functorial flat resolutions, then so does `Mod C R`, by the free modules
`R ⊗ F` on flat objects `F` of `C`. -/
instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry

end CategoryTheory.Mod
