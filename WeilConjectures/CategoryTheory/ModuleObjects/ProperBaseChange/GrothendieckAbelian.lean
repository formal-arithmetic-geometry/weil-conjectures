/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!
Declarations of ours that lived in the upstream file
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` (moved out by the
scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live).
-/

/-!

# Module objects in a closed symmetric monoidal Grothendieck abelian category

Let `C` be a closed symmetric monoidal Grothendieck abelian category whose tensor product is
additive, and let `R : C` be a commutative algebra object. The category `Mod C R` of
`R`-module objects is abelian (`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`) and
symmetric monoidal for the relative tensor product `⊗_R`
(`WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`). This file records that `Mod C R`
inherits the remaining properties of `C` needed by the K-flat machinery:

* `Mod.monoidalClosed`: `Mod C R` is closed monoidal;
* `Mod C R` is Grothendieck abelian, as an instance deduced from `Mod.isGrothendieckAbelian`;
* `Mod.hasFunctorialFlatResolution`: `Mod C R` admits functorial flat resolutions if `C` does.

## Sorried input

The instances `Mod.monoidalClosed` and `Mod.hasFunctorialFlatResolution` are currently `sorry`ed.
The intended arguments are:

* The internal hom `Hom_R(M, N)` is the equalizer of the two maps `[M, N] ⇉ [R ⊗ M, N]`, adjoint
  to `R ⊗ M ⊗ [M, N] ⟶ R ⊗ N ⟶ N` and to `R ⊗ M ⊗ [M, N] ⟶ M ⊗ [M, N] ⟶ N`, with the
  `R`-action induced by that of `N`.
* If `F` is flat in `C`, then `R ⊗ F` is flat in `Mod C R` because `(R ⊗ F) ⊗_R M ≅ F ⊗ M`; and
  a functorial flat resolution `P(M) ⟶ M` in `C` gives the functorial epimorphism
  `R ⊗ P(M) ⟶ R ⊗ M ⟶ M` of `R`-modules.

-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

end CategoryTheory.Mod
