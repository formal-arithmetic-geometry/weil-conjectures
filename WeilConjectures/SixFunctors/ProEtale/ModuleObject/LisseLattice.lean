/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeFiniteCover

/-!
# Lattices of lisse `E`-sheaves on regular schemes

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `S`
a connected regular Noetherian scheme. Every lisse (locally free) `E_S`-module `L` has a lattice:
there is a locally free `𝒪_{E,S}`-module `L₀` with `E_S ⊗_{𝒪_{E,S}} L₀ ≅ L`
(`AlgebraicGeometry.ProEtale.exists_isLocallyFree_padicIntegers_extendScalars_iso`, blueprint
`sk-lem-stratified-lattice`, first stage).

The proof:

* `L` is trivialised on a finite pro-étale cover by affine schemes
  (`ProEtale.CondensedRing.exists_finite_affine_cover_isFree_upperStar`), with a single rank, `S`
  being connected (`AlgebraicGeometry.ProEtale.rank_eq_of_comp_eq`);
* the values of the transition matrices of the trivialisations form a continuous `GL_n(E)`-valued
  cocycle (`AlgebraicGeometry.ProEtale.exists_transitionValues`);
* on the regular scheme `S`, the cocycle is conjugate to a `GL_n(𝒪_E)`-valued one by a lattice-
  valued twisted section (`AlgebraicGeometry.exists_integral_conj_of_transitionValues`, from the
  lattice theorem `AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice`);
* the trivialisations changed accordingly have integral transition matrices, so the lattices
  spanned by the bases glue to `L₀`
  (`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

end AlgebraicGeometry.ProEtale
