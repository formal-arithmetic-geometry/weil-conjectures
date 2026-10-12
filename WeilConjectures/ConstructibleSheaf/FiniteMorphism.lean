/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Finite.Counit

/-!
# Finite direct images of constructible sheaves on Noetherian schemes

Let `Λ` be a finite commutative ring. For a finite morphism `h : V ⟶ U` of schemes with `U`
Noetherian:

- `AlgebraicGeometry.Etale.exists_dense_isFiniteLocallyConstantSheaf_lowerStar` (blueprint
  `lem-weil-pbc-finite-pushforward-generic-constructible`): over an integral Noetherian affine
  base, the direct image of a constructible sheaf is finite locally constant on a dense open.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isFinite` (blueprint
  `lem-weil-pbc-finite-pushforward-constructible-noetherian`): the direct image `h_* E` of a
  constructible sheaf is constructible.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_lowerStar_of_isFinite` (blueprint
  `lem-fin-finite-reflects-constructibility`): conversely, if `h_* F` is constructible and `V`
  is Noetherian, then `F` is constructible.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-weil-pbc-finite-pushforward-generic-constructible`: Generic finite pushforward
is constructible.

Let `S` be an integral Noetherian affine scheme, `g : Z ⟶ S` a finite morphism and `E` a
constructible sheaf of `Λ`-modules on `Z_ét`. Then there is a dense open `S° ⊆ S` on which the
direct image `g_* E` is finite locally constant (lisse). -/
theorem Etale.exists_dense_isFiniteLocallyConstantSheaf_lowerStar {S Z : Scheme.{u}}
    [IsIntegral S] [IsAffine S] [IsNoetherian S] (g : Z ⟶ S) [IsFinite g]
    (E : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf E] :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      IsFiniteLocallyConstantSheaf
        ((U.ι)^*[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj E)) :=
  sorry

/-- Blueprint `lem-weil-pbc-finite-pushforward-constructible-noetherian`: Finite pushforward
preserves constructibility on Noetherian schemes.

Let `U` be Noetherian, `h : V ⟶ U` finite and `E` a constructible sheaf of `Λ`-modules on
`V_ét`. Then its direct image `h_* E` is constructible on `U_ét`. -/
theorem Scheme.IsConstructibleSheaf.lowerStar_of_isFinite {U V : Scheme.{u}} [IsNoetherian U]
    (h : V ⟶ U) [IsFinite h] (E : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf E] : IsConstructibleSheaf ((h)_*[ModuleCat.{u + 1} Λ].obj E) :=
  sorry

/-- Blueprint `lem-fin-finite-reflects-constructibility`: Finite direct image reflects
constructibility.

Let `p : Z ⟶ S` be a finite morphism of Noetherian schemes and `F` an étale sheaf of
`Λ`-modules on `Z`. If its direct image `p_* F` is constructible, then `F` is constructible. -/
theorem Scheme.IsConstructibleSheaf.of_lowerStar_of_isFinite {Z S : Scheme.{u}} [IsNoetherian Z]
    [IsNoetherian S] (p : Z ⟶ S) [IsFinite p] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf ((p)_*[ModuleCat.{u + 1} Λ].obj F)) : IsConstructibleSheaf F :=
  sorry

end AlgebraicGeometry

end
