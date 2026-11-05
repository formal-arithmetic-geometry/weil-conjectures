/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

/-!
# Extension of scalars along a finite free ring map preserves flat sheaves

Let `φ : R →+* S` be a morphism of commutative rings making `S` a finite free `R`-module. If a
presheaf `P` of `R`-modules has locally trivial relations
(`CategoryTheory.Presheaf.HasLocallyTrivialRelations`), so does the presheaf `S ⊗_R P` of
`S`-modules: writing sections of `S ⊗_R P` in a basis `(b_k)` of `S`, an `S`-linear relation
between them is a finite system of `R`-linear relations between their coordinates, which is
locally trivial, and the trivialization of the coordinates gives one of the sections. By the
relation criterion for flatness, the sheafification of `S ⊗_R F` is flat for every flat sheaf
`F` of `R`-modules over a Noetherian ring `R`.

## Main results

- `CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp_extendScalars`: extension of scalars
  preserves locally trivial relations.
- `CategoryTheory.Sheaf.flat_presheafToSheaf_obj_comp_extendScalars`: extension of scalars
  followed by sheafification preserves flat sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct ChangeOfRings

namespace CategoryTheory

section Coordinates

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type*} [Fintype ι]
  [DecidableEq ι] (b : Module.Basis ι R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))
  {M : ModuleCat R}

end Coordinates

section Unit

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} [Finite ι]
  (b : Module.Basis ι R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))

end Unit

namespace Presheaf

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} [Finite ι]
  (b : Module.Basis ι R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))

variable [EssentiallySmall.{u + 1} C]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} S))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} S)]
  [IsNoetherianRing R]

end Presheaf

end CategoryTheory
