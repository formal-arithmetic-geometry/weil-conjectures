/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# Descent of lisse `ℚ̄_ℓ`-sheaves to a finite subextension

Let `ℓ` be a prime and `S` a quasi-compact quasi-separated scheme. Every lisse (finite locally
free) `ℚ̄_ℓ,S`-module `L` is the extension of scalars `ℚ̄_ℓ,S ⊗_{E_S} L_E` of a lisse
`E_S`-module `L_E`, for some finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`
(`ProEtale.exists_isLocallyFree_extendScalars_iso`, blueprint
`det-lem-coefficient-finite-descent-lisse` (1)).

The proof: `S` being quasi-compact, `L` is trivialised on finitely many affine pro-étale charts;
the transition matrices have finitely many entries in the sections of `ℚ̄_ℓ,S = colim_E E_S`
over quasi-compact quasi-separated objects, which commute with the filtered colimit, hence lie
in some `E_S`; the cocycle then glues to a lisse `E_S`-module.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Blueprint `det-lem-coefficient-finite-descent-lisse` (1): for a quasi-compact
quasi-separated scheme `S` and a lisse `ℚ̄_ℓ,S`-module `L`, there are a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a lisse `E_S`-module `L_E` with `ℚ̄_ℓ,S ⊗_{E_S} L_E ≅ L`. See the
module docstring. -/
theorem exists_isLocallyFree_extendScalars_iso (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S]
    (L : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (padicAlgClRingObj S ℓ))
    (hL : IsLocallyFree (padicAlgClRingObj S ℓ) L) :
    ∃ (E : FiniteIntermediateField ℓ)
      (L' : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (padicSubfieldRingObj S ℓ E)),
      IsLocallyFree (padicSubfieldRingObj S ℓ E) L' ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl S ℓ E)).obj L' ≅ L) :=
  sorry

end AlgebraicGeometry.ProEtale
