/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendChangeTransfer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars

/-!
# The transitivity of the derived extensions of scalars on complexes

For finite subextensions `E ≤ F` of `ℚ̄_ℓ`, the transitivity isomorphism
`T^X_{E,F} ⋙ T^X_{F,Ω} ≅ T^X_{E,Ω}` (`ProEtale.derivedExtendScalarsCompIso`) is, on the image
of an object `M` of the homotopy category and modulo the counits of the derived extensions of
scalars (which are isomorphisms, the extensions of scalars being exact), induced by the
isomorphism `ℚ̄_ℓ,X ⊗_{F_X} (F_X ⊗_{E_X} -) ≅ ℚ̄_ℓ,X ⊗_{E_X} -` on the homotopy categories
(`ProEtale.derivedExtendScalarsCompIso_hom_app_Qh`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale
