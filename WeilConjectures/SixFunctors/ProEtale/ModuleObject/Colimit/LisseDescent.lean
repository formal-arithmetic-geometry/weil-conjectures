/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsFreeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeFiniteCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PadicAlgClSections

/-!
# Descent of lisse `ℚ̄_ℓ`-sheaves to a finite subextension

Let `ℓ` be a prime and `S` a quasi-compact quasi-separated scheme. Every lisse (finite locally
free) `ℚ̄_ℓ,S`-module `L` is the extension of scalars `ℚ̄_ℓ,S ⊗_{E_S} L_E` of a lisse
`E_S`-module `L_E`, for some finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`ProEtale.exists_isLocallyFree_extendScalars_iso`, blueprint
`det-lem-coefficient-finite-descent-lisse` (1)).

The proof: `S` being quasi-compact, `L` is trivialised on a finite pro-étale cover by affine
schemes `V_k` (`ProEtale.CondensedRing.exists_finite_affine_cover_isFree_upperStar`). The fibre
products `V_j ×_S V_k` are quasi-compact and quasi-separated, so the global sections of
`ℚ̄_ℓ = colim_E E` over them are the filtered colimit of those of the `E`
(`ProEtale.exists_subfieldToPadicAlgClSection_eq`, blueprint
`det-lem-coefficient-finite-descent-sections` (2)): the finitely many entries of the transition
matrices and of their inverses come from a common `E_{V_j ×_S V_k}`
(`ProEtale.exists_forall_le_isDefinedOver`). The lattices spanned by the bases then glue to a
lisse `E_S`-module
(`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver`),
the units `E^n ⟶ ℚ̄_ℓ^n` being split injective by the retraction `ℚ̄_ℓ ⟶ E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale
