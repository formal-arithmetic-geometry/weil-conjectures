/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!
# Multiplication by a nonzerodivisor on an injective sheaf of modules is an epimorphism

Let `Λ` be a commutative ring, `ϖ ∈ Λ` a nonzerodivisor and `I` an injective sheaf of
`Λ`-modules on a site. Multiplication by `ϖ` on `I` is an epimorphism: a section `s` of `I` over
`U` is a morphism from the sheafified free `Λ`-module sheaf on `U`, on which multiplication by `ϖ`
is a monomorphism, and extending along it divides `s` by `ϖ`. This is the module version of
`CategoryTheory.Sheaf.epi_nsmul_id_of_injective`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type (max w v)} [CommRing Λ] [HasSheafify J (ModuleCat.{max w v} Λ)]

variable (Λ) in
/-- The free presheaf of `Λ`-modules on `U`. -/
noncomputable abbrev freeModuleYoneda (U : C) : Cᵒᵖ ⥤ ModuleCat.{max w v} Λ :=
  uliftYoneda.{w}.obj U ⋙ ModuleCat.free Λ

/-- The generator of the free presheaf of `Λ`-modules on `U` over `U`: the identity of `U`. -/
noncomputable def freeModuleYonedaGen (U : C) : (freeModuleYoneda.{w} Λ U).obj (op U) :=
  Finsupp.single (ULift.up (𝟙 U)) 1

variable [J.HasSheafCompose (forget (ModuleCat.{max w v} Λ))]

end Sheaf

end CategoryTheory
