/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ConstructibleExtContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimitHomSurjTransfer

/-!
# (Hom)-surjectivity of the cocone of bounded constructible categories

Let `ℓ` be a prime, `X` a topologically noetherian scheme and `E, F` finite subextensions of
`ℚ̄_ℓ`. Every morphism `f : T^X_{E,Ω} K ⟶ T^X_{F,Ω} L` from the extension of scalars of a bounded
constructible `E_X`-complex `K` to that of a bounded below `F_X`-complex `L` is of the form
`τ⁻¹ ≫ T^X_{H,Ω} g ≫ τ` for a finite subextension `H ⊇ E, F` and a morphism
`g : T^X_{E,H} K ⟶ T^X_{F,H} L` (`ProEtale.exists_derivedExtendScalarsToPadicAlgCl_map_eq`,
blueprint `lem-sfb-constructible-cocone-hom-surj`).

Represent `L` by a complex `Y` of `F_X`-modules vanishing below some degree. By adjunction, `f`
corresponds to a morphism `K ⟶ D(Res_{E→Ω})(ℚ̄_ℓ,X ⊗_{F_X} Y)`, and
`Res_{E→Ω}(ℚ̄_ℓ,X ⊗_{F_X} Y) = colim_k Res_{E→k}(k_X ⊗_{F_X} Y)` is a filtered colimit of complexes
vanishing below the same degree (`ProEtale.isColimitSubfieldExtendScalarsCocone`). By the
continuity of `Hom` out of `K`
(`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj`),
it factors through some `Res_{E→k}(k_X ⊗_{F_X} Y)`, which is identified with the adjoint transfer
of the transitivity isomorphisms (`ProEtale.compIsoTransfer_derivedExtendScalars_Qh`), and one
concludes by `CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale
