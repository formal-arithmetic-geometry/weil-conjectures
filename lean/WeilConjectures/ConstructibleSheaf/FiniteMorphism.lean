/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.SixFunctors.Finite.Counit

import Sheaf.AlgebraicGeometry.GenericFinitePushforward
import Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.ConstructibleModuleUnderlyingSets
import WeilConjectures.ConstructibleSheaf.OfForget
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures

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

private theorem finiteLocallyConstant_of_setPullback
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsLisseEtaleSheafOfSets ((etaleSetPullback g).obj
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))) :
    IsFiniteLocallyConstantSheaf ((g)^*[ModuleCat.{u + 1} Λ].obj F) := by
  obtain ⟨em⟩ := pullback_forget_modules_iso Λ g F
  let ea := (etaleInverseImageAlgebraicStructures Y X g).2.choose
  let e := (sheafCompose Y.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso em ≪≫
      ea.app ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
  exact IsFiniteLocallyConstantSheaf.of_forget _ (Scheme.lisse_of_iso e.symm hF)

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
        ((U.ι)^*[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj E)) := by
  let Eab := (sheafCompose Z.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj E
  have hE := isConstructibleEtaleSheafOfSets_of_module Λ E
    ((isConstructibleEtaleModuleSheaf_iff E).mpr inferInstance)
  obtain ⟨U, hU, hL⟩ := exists_dense_open_lisse_finite_directImage S g Eab hE
  exact ⟨U, hU, finiteLocallyConstant_of_setPullback U.ι
    ((g)_*[ModuleCat.{u + 1} Λ].obj E) hL⟩

/-- Blueprint `lem-weil-pbc-finite-pushforward-constructible-noetherian`: Finite pushforward
preserves constructibility on Noetherian schemes.

Let `U` be Noetherian, `h : V ⟶ U` finite and `E` a constructible sheaf of `Λ`-modules on
`V_ét`. Then its direct image `h_* E` is constructible on `U_ét`. -/
theorem Scheme.IsConstructibleSheaf.lowerStar_of_isFinite {U V : Scheme.{u}} [IsNoetherian U]
    (h : V ⟶ U) [IsFinite h] (E : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf E] : IsConstructibleSheaf ((h)_*[ModuleCat.{u + 1} Λ].obj E) := by
  let Eab := (sheafCompose V.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj E
  have hE := isConstructibleEtaleSheafOfSets_of_module Λ E
    ((isConstructibleEtaleModuleSheaf_iff E).mpr inferInstance)
  obtain ⟨S, hS⟩ := isConstructibleEtaleSheafOfSets_lowerStar_of_isNoetherian h Eab hE
  exact ⟨S, fun i ↦ finiteLocallyConstant_of_setPullback (S.immersion i)
    ((h)_*[ModuleCat.{u + 1} Λ].obj E) (hS i)⟩

/-- Blueprint `lem-fin-finite-reflects-constructibility`: Finite direct image reflects
constructibility.

Let `p : Z ⟶ S` be a finite morphism of Noetherian schemes and `F` an étale sheaf of
`Λ`-modules on `Z`. If its direct image `p_* F` is constructible, then `F` is constructible. -/
theorem Scheme.IsConstructibleSheaf.of_lowerStar_of_isFinite {Z S : Scheme.{u}} [IsNoetherian Z]
    [IsNoetherian S] (p : Z ⟶ S) [IsFinite p] (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf ((p)_*[ModuleCat.{u + 1} Λ].obj F)) : IsConstructibleSheaf F := by
  let ε := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).counit.app F
  have : IsConstructibleSheaf
      (((p)_*[ModuleCat.{u + 1} Λ] ⋙ (p)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    IsConstructibleSheaf.upperStar p ((p)_*[ModuleCat.{u + 1} Λ].obj F)
  have : IsConstructibleSheaf (Limits.kernel ε) := IsConstructibleSheaf.of_mono
    (F := ((p)_*[ModuleCat.{u + 1} Λ] ⋙ (p)^*[ModuleCat.{u + 1} Λ]).obj F) (kernel.ι ε)
  have : IsConstructibleSheaf (Limits.cokernel (kernel.ι ε)) := IsConstructibleSheaf.cokernel _
  let e : Limits.cokernel (kernel.ι ε) ≅ F :=
    (cokernelIsCokernel (kernel.ι ε)).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
  exact IsConstructibleSheaf.of_iso e

end AlgebraicGeometry

end
