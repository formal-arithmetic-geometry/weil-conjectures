/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.HomSheafAcyclic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# Restriction of scalars of injective sheaves is acyclic

Let `φ : Λ →+* Λ'` be a morphism of commutative rings and `J` a Grothendieck topology. The
restriction of scalars `res J` of an injective sheaf `I` of `Λ'`-modules is in general not an
injective sheaf of `Λ`-modules, but it is acyclic for every left exact functor `Φ` on sheaves of
`Λ`-modules which sends the morphisms that are surjective on sections to epimorphisms
(`CategoryTheory.Sheaf.rightAcyclic_restrictScalars_obj_of_injective`), e.g. for direct images.

Indeed, embedding `res I` into an injective sheaf `E` of `Λ`-modules, the adjoint morphism
`I ⟶ Hom_Λ(Λ', E)` is a split monomorphism, so `res I` is a direct summand of
`res Hom_Λ(Λ', E)`, which is the sheaf `Hom_Λ(Λ', E)` of homomorphisms out of the `Λ`-module
`Λ'` (`CategoryTheory.Sheaf.restrictScalarsCoextendScalarsObjIso`), and this sheaf is
`Φ`-acyclic (`CategoryTheory.Sheaf.rightAcyclic_homSheaf_obj`).

This is the input for the commutation of derived direct images with restriction of scalars, on
any site.
-/

@[expose] public section

universe t w v

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

section

variable {Λ Λ' : Type t} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

end

variable {Λ Λ' : Type (max w v)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

variable {C : Type (max w v)} [Category.{v} C] (J : GrothendieckTopology C)

variable [HasSheafify J (ModuleCat.{max w v} Λ)] [HasSheafify J (ModuleCat.{max w v} Λ')]
  [HasInjectiveResolutions (Sheaf J (ModuleCat.{max w v} Λ))]
  [EnoughInjectives (Sheaf J (ModuleCat.{max w v} Λ))]

end CategoryTheory.Sheaf
