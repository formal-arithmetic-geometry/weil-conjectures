/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FinitePushforward.GenericFactorization
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphismDescent
public import WeilConjectures.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Generic local constancy of finite direct images of finite locally constant sheaves

Let `S` be an integral Noetherian affine scheme, `g : Z ⟶ S` finite and `E` a finite locally
constant sheaf of `Λ`-modules on `Z_ét`, `Λ` a finite ring. Then `g_* E` is finite locally
constant over a nonempty open of `S`
(`AlgebraicGeometry.Etale.exists_isOpenImmersion_isFiniteLocallyConstantSheaf_lowerStar`).

Factor `g` generically as in
`AlgebraicGeometry.Scheme.Hom.exists_isUniversalHomeomorphism_etale_isPullback`: there are
universal homeomorphisms `a : Y ⟶ Z`, `u : Y ⟶ T` and a finite `t : T ⟶ S`, étale over a
nonempty open `j : S' ⟶ S`, with `a ≫ g = u ≫ t`. Pullback and pushforward along universal
homeomorphisms are inverse equivalences, so `g_* E ≅ t_* u_* a^* E` with `u_* a^* E` finite
locally constant (`IsFiniteLocallyConstantSheaf.of_upperStar_of_isUniversalHomeomorphism`).
By finite base change, `j^* t_* u_* a^* E` is the direct image along the finite étale base
change of `t` of a finite locally constant sheaf, hence finite locally constant
(`AlgebraicGeometry.Scheme.finiteLocallyConstant_lowerStar_of_finite_etale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The direct image of a finite locally constant sheaf along a finite morphism `g : Z ⟶ S` to an
integral Noetherian affine scheme is finite locally constant over a nonempty open of `S`. -/
theorem Etale.exists_isOpenImmersion_isFiniteLocallyConstantSheaf_lowerStar {S Z : Scheme.{u}}
    [IsIntegral S] [IsAffine S] [IsNoetherian S] (g : Z ⟶ S) [IsFinite g]
    (E : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf E] :
    ∃ (S' : Scheme.{u}) (j : S' ⟶ S), IsOpenImmersion j ∧ Nonempty S' ∧
      IsFiniteLocallyConstantSheaf
        ((j)^*[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj E)) := by
  obtain ⟨Y, T, S', T', a, u, t, j, j', t', ha, hu, ht, hcomm, hj, hS', hpb, ht'⟩ :=
    g.exists_isUniversalHomeomorphism_etale_isPullback
  have : IsFinite t' := MorphismProperty.of_isPullback (P := @IsFinite) hpb ht
  -- `G = u_* a^* E` is finite locally constant on `T`
  let G := (u)_*[ModuleCat.{u + 1} Λ].obj ((a)^*[ModuleCat.{u + 1} Λ].obj E)
  have := IsFiniteLocallyConstantSheaf.upperStar a E
  have := Etale.isEquivalence_lowerStar (ModuleCat.{u + 1} Λ) u
  have := Etale.isEquivalence_upperStar (ModuleCat.{u + 1} Λ) a
  have : IsFiniteLocallyConstantSheaf ((u)^*[ModuleCat.{u + 1} Λ].obj G) :=
    IsFiniteLocallyConstantSheaf.of_iso (F := (a)^*[ModuleCat.{u + 1} Λ].obj E) (asIso
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) u).counit.app _)).symm
  have : IsFiniteLocallyConstantSheaf G :=
    IsFiniteLocallyConstantSheaf.of_upperStar_of_isUniversalHomeomorphism u G
  -- `g_* E ≅ t_* G`
  let e₁ : (g)_*[ModuleCat.{u + 1} Λ].obj E ≅ (t)_*[ModuleCat.{u + 1} Λ].obj G :=
    ((g)_*[ModuleCat.{u + 1} Λ]).mapIso
      (asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).unit.app E)) ≪≫
    (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) a g (u ≫ t) hcomm.symm).app _ ≪≫
    ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) u t).app _).symm
  -- finite base change along `j`
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) hpb
  let e₂ := asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) hpb.toCommSq).app G)
  have := IsFiniteLocallyConstantSheaf.upperStar j' G
  have := finiteLocallyConstant_lowerStar_of_finite_etale t'
    ((j')^*[ModuleCat.{u + 1} Λ].obj G)
  exact ⟨S', j, hj, hS', IsFiniteLocallyConstantSheaf.of_iso
    (F := (t')_*[ModuleCat.{u + 1} Λ].obj ((j')^*[ModuleCat.{u + 1} Λ].obj G))
    (((j)^*[ModuleCat.{u + 1} Λ]).mapIso e₁ ≪≫ e₂).symm⟩

end AlgebraicGeometry
