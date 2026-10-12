/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Normalization comparison objects on the isomorphism locus

Source: normalization exact-sequence blueprint, unit `sk-thm-p1`.
(blueprint: lem-weil-pbc-normalization-comparison-on-iso-locus)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The normalization comparison objects agree on the isomorphism locus.

Source: normalization exact-sequence blueprint,
`sec-proper-base-change/sk-thm-p1/lemma-weil-pbc-normalization-exact-sequence.md`,
identification over the isomorphism locus.
(blueprint: lem-weil-pbc-normalization-comparison-on-iso-locus)

Proof: Form W = ν⁻¹(V) and T = U ×_X V. The restricted map ν_V : W → V is an
isomorphism by assumption. Finite base change identifies the restriction of the target
with (ν_V)_* of the restriction of j'_!R to W. Base change for extension by zero
identifies this with extension by zero on U' ×_X V of the pulled-back constant sheaf.
The given Cartesian square and ν_V identify U' ×_X V with T and its immersion into W
with T → V. Constant-sheaf pullback identifies both coefficient sheaves with R on T.
Pushforward along ν_V therefore gives extension by zero of R along T → V, which is
also the restriction of j_!R by extension-by-zero base change. This proves the stated
isomorphism of objects. No particular comparison map is claimed to be invertible.
Density, curve hypotheses, and finiteness of R are unnecessary. Empty opens and zero
coefficients yield the same identification of zero objects. -/
theorem normalization_comparison_on_iso_locus {X X' U U' : Scheme.{u}}
    (ν : X' ⟶ X) [IsFinite ν] (V : X.Opens) [IsIso (ν ∣_ V)]
    (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'} [IsOpenImmersion j']
    {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ) :
    Nonempty (((V.ι)^*[ModuleCat.{u + 1} Λ].obj
      ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))) ≅
      ((V.ι)^*[ModuleCat.{u + 1} Λ].obj ((ν)_*[ModuleCat.{u + 1} Λ].obj
        ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))))) := by
  sorry
end AlgebraicGeometry
