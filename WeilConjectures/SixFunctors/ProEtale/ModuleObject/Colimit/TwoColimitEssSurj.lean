/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitEssSurjGenerators

/-!
# (Obj): descent of bounded constructible `ℚ̄_ℓ`-complexes

Let `ℓ` be a prime and `X` a scheme with noetherian underlying space. Assuming
**(Hom)**-surjectivity for the extensions of scalars from the finite subextensions
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, every bounded constructible `ℚ̄_ℓ,X`-complex `K` is isomorphic to
`T^X_{E,Ω} K_E = ℚ̄_ℓ,X ⊗ᴸ_{E_X} K_E` for some finite subextension `E` and some bounded
constructible `E_X`-complex `K_E`
(`ProEtale.exists_iso_derivedExtendScalarsToPadicAlgCl_obj`, blueprint
`lem-sfb-constructible-cocone-obj`, `det-lem-coefficient-finite-descent-objects`).

The complexes which descend in this sense (`ProEtale.descendsToPadicSubfield`) form a class closed
under isomorphisms and extensions in distinguished triangles (the cone step,
`ProEtale.descendsToPadicSubfield_obj₂`) and under shifts, which contains the generators
`a_! L` of `Dᵇc(X, ℚ̄_ℓ)` (`ProEtale.descendsToPadicSubfield_lowerShriek`). By the generation of
`Dᵇc(X, ℚ̄_ℓ)` by the `(a_! L)[n]`
(`ProEtale.CondensedRing.boundedConstructible_le_of_lowerShriek_isLocallyFree`), it contains
every bounded constructible complex.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

end AlgebraicGeometry.ProEtale
