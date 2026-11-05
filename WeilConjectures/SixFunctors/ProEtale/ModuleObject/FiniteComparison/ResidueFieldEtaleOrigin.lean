/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# The reduction of a bounded constructible `𝒪_E`-complex is of étale origin

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with residue field `𝔽_E` and `X` a noetherian
scheme. For a bounded constructible complex `K₀` of `𝒪_{E,X}`-module objects, the reduction
`K₀ ⊗ᴸ_{𝒪_{E,X}} 𝔽̲_{E,X}`, read through the finite-coefficient comparison
`ProEtale.finiteCoefficientDerivedEquivalence` as a complex of pro-étale sheaves of
`𝔽_E`-modules, is bounded constructible
(`ProEtale.CondensedRing.boundedConstructible_finiteCoefficientDerivedEquivalence_residueField`),
hence bounded below of étale origin
(`ProEtale.CondensedRing.plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
