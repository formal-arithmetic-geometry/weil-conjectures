/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.CompIsoTransfer
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjCounit

/-!
# The adjoint transfer of the derived extensions of scalars on complexes

Let `E, F ≤ k` be finite subextensions of `ℚ̄_ℓ`. Along the adjunctions
`T^X_{E,k} ⊣ D(Res_{E→k})`, `T^X_{E,Ω} ⊣ D(Res_{E→Ω})` and the transitivity isomorphisms
`T^X_{E,k} ⋙ T^X_{k,Ω} ≅ T^X_{E,Ω}`, `T^X_{F,k} ⋙ T^X_{k,Ω} ≅ T^X_{F,Ω}`, a morphism
`T^X_{E,Ω} K ⟶ T^X_{F,Ω} L` is of the form `τ⁻¹ ≫ T^X_{k,Ω} g ≫ τ` as soon as its adjoint
`K ⟶ D(Res_{E→Ω}) T^X_{F,Ω} L` factors through the adjoint transfer
`D(Res_{E→k}) T^X_{F,k} L ⟶ D(Res_{E→Ω}) T^X_{F,Ω} L`
(`CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`).

On the image `L = Q Y` of a complex, this transfer is, modulo the counits of the derived
extensions of scalars and the factorizations of `D(Res)`, the image of the inclusion
`Res_{E→k}(k_X ⊗_{F_X} Y) ⟶ Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y)` of the colimit cocone
`ProEtale.subfieldExtendScalarsCocone`
(`ProEtale.compIsoTransfer_derivedExtendScalars_Qh`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {E F G : FiniteIntermediateField ℓ}
  (hE : E ≤ G) (hF : F ≤ G)
  (Y : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ)

end AlgebraicGeometry.ProEtale
