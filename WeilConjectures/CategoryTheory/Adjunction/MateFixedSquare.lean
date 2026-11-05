/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Exchange transformations across a base-change square

Consider a commutative square of "spaces" `F --ι--> C --c--> P` and `F --d--> X --Δ--> P`, with
`ι` and `Δ` proper, encoded on categories of sheaves `DC, DF, DX, DP` by

* adjunctions `c_! ⊣ c^!` and `d_! ⊣ d^!` (`cL ⊣ cR`, `dL ⊣ dR`);
* adjunctions `ι^* ⊣ ι_*` and `Δ^* ⊣ Δ_*` (`ιU ⊣ ιS`, `ΔU ⊣ ΔS`), together with functors
  `ι_!`, `Δ_!` (`ιL`, `ΔL`) and isomorphisms `ι_! ≅ ι_*`, `Δ_! ≅ Δ_*`;
* the composition isomorphism `Sq : ι_! ⋙ c_! ≅ d_! ⋙ Δ_!` and the base change isomorphism
  `BC : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!`, assumed to be the mate of `Sq`;
* the exceptional base change `B : Δ_* ⋙ c^! ≅ d^! ⋙ ι_*`, the conjugate of `BC⁻¹`;

and the same data on a second row (primed). Let `Ψ_C, Ψ_F, Ψ_X, Ψ_P` be functors from the first
row to the second, with

* pullback exchanges `α_ι : Ψ_C ⋙ ι'^* ⟶ ι^* ⋙ Ψ_F` and `α_Δ : Ψ_P ⋙ Δ'^* ⟶ Δ^* ⋙ Ψ_X`, and
  their mates, the proper exchanges `χ_ι : ι_* ⋙ Ψ_C ⟶ Ψ_F ⋙ ι'_*` and
  `χ_Δ : Δ_* ⋙ Ψ_P ⟶ Ψ_X ⋙ Δ'_*`;
* compact-support exchanges `ν_c, ν_d, ν_ι, ν_Δ` (`ν_f : Ψ ⋙ f'_! ⟶ f_! ⋙ Ψ`), with `ν_ι`, `ν_Δ`
  inverse to `χ_ι`, `χ_Δ` under `ι_! ≅ ι_*`, `Δ_! ≅ Δ_*`, and compatible with the composition
  `cι = Δd`;
* the exceptional exchanges `β_c`, `β_d`, the mates of `ν_c`, `ν_d`.

Then the *fixed-square identity*

```
Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ c'^!(χ_Δ) ∘ β_c(Δ_*)
```

holds (`CategoryTheory.fixedSquare_of_compactSupportExchange`). This is the abstract form of
blueprint `sk-lem-tf-nearby-mate-coherences` (6), proved as in the blueprint: after taking
adjoints, both sides are the exchange of the composite `cι = Δd` followed by the counit of
`d_! ⊣ d^!`.

-/

@[expose] public section

namespace CategoryTheory

variable {DC DF DX DP DC' DF' DX' DP' : Type*} [Category DC] [Category DF] [Category DX]
  [Category DP] [Category DC'] [Category DF'] [Category DX'] [Category DP']
  {cL : DC ⥤ DP} {cR : DP ⥤ DC} {dL : DF ⥤ DX} {dR : DX ⥤ DF}
  {ιU : DC ⥤ DF} {ιS : DF ⥤ DC} {ιL : DF ⥤ DC} {ΔU : DP ⥤ DX} {ΔS : DX ⥤ DP} {ΔL : DX ⥤ DP}
  {cL' : DC' ⥤ DP'} {cR' : DP' ⥤ DC'} {dL' : DF' ⥤ DX'} {dR' : DX' ⥤ DF'}
  {ιU' : DC' ⥤ DF'} {ιS' : DF' ⥤ DC'} {ιL' : DF' ⥤ DC'} {ΔU' : DP' ⥤ DX'} {ΔS' : DX' ⥤ DP'}
  {ΔL' : DX' ⥤ DP'}
  (adjc : cL ⊣ cR) (adjd : dL ⊣ dR) (adjι : ιU ⊣ ιS) (adjΔ : ΔU ⊣ ΔS)
  (adjc' : cL' ⊣ cR') (adjd' : dL' ⊣ dR') (adjι' : ιU' ⊣ ιS') (adjΔ' : ΔU' ⊣ ΔS')
  (isoι : ιL ≅ ιS) (isoΔ : ΔL ≅ ΔS) (isoι' : ιL' ≅ ιS') (isoΔ' : ΔL' ≅ ΔS')
  (Sq : ιL ⋙ cL ≅ dL ⋙ ΔL) (Sq' : ιL' ⋙ cL' ≅ dL' ⋙ ΔL')
  (BC : cL ⋙ ΔU ≅ ιU ⋙ dL) (BC' : cL' ⋙ ΔU' ≅ ιU' ⋙ dL')
  {ΨC : DC ⥤ DC'} {ΨF : DF ⥤ DF'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
  (αι : ΨC ⋙ ιU' ⟶ ιU ⋙ ΨF) (αΔ : ΨP ⋙ ΔU' ⟶ ΔU ⋙ ΨX)
  (νc : ΨC ⋙ cL' ⟶ cL ⋙ ΨP) (νd : ΨF ⋙ dL' ⟶ dL ⋙ ΨX)
  (νι : ΨF ⋙ ιL' ⟶ ιL ⋙ ΨC) (νΔ : ΨX ⋙ ΔL' ⟶ ΔL ⋙ ΨP)

section

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ : E ⥤ F} {R₂ R₂' : F ⥤ E}

end

end CategoryTheory
