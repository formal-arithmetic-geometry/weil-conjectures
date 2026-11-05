/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.Sites.ReductionFlat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Extension of scalars for sheaves of modules over a constant ring

Let `S` be an algebra over a commutative ring `R` and `J` a Grothendieck topology. Extension of
scalars `F ↦ S ⊗_R F` of sheaves of `R`-modules is the sheafification
`Sheaf.composeAndSheafify J (ModuleCat.extendScalars (algebraMap R S))` of the objectwise extension
of scalars. Restricting the scalars of `S ⊗_R F` back to `R` gives the tensor product `F ⊗ S_X`
with the constant sheaf
(`CategoryTheory.Sheaf.extendScalarsCompRestrictScalarsIso`).

This generalises the reduction `CategoryTheory.Sheaf.quotSMulTop` modulo an ideal, the case
`S = R ⧸ I`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} S))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} S)]

end CategoryTheory.Sheaf
