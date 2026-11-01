/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekPullback
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperStar

/-!
# The reduction square for the pullbacks, and the proper piece of the reduction square for `Rf_!`

Write `Ψ` for the derived extension of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site,
`Res` for the restriction of scalars and `T : red_{n+1} ⟶ red_n ⋙ Res` for the transpose of the
compatibility `β : Ψ(red_{n+1} K) ≅ red_n K` of `Ψ` with the reductions
(`ProEtale.CondensedRing.etaleReductionTransposeNatTrans`). This file (blueprint
`det-sp-purity-coefficient-change`) states:

* `ProEtale.CondensedRing.etaleReductionUpperStarIso_restrictScalars`: for any `f : Z ⟶ Y`, the
  canonical comparisons `f^* ⋙ red ≅ red ⋙ Lf^*` modulo `ℓⁿ⁺¹` and `ℓⁿ`
  (`ProEtale.CondensedRing.etaleReductionUpperStarIso`) are intertwined by `T` and the commutation
  of `Res` with `Lf^*` (`Etale.leftDerivedUpperStarRestrictScalarsIso`); it is assembled
  (`CategoryTheory.map_comp_app_comp_map_eq_of_cube`) from the étale and pro-étale pieces of
  `WeilConjectures.SmoothPurity.OrientationTransitionUpperStar`;
* `ProEtale.CondensedRing.mateEquiv_etaleReductionUpperStarIso_inv`: for a proper `p`, the
  comparison `Rp_! ⋙ red ≅ red ⋙ Rp_!` (`ProEtale.CondensedRing.etaleReductionLowerShriekIso`),
  followed by `Rp_! ≅ Rp_*`, is the mate of the pullback comparison under `p^* ⊣ Rp_!` and
  `Lp^* ⊣ Rp_*`;
* `Etale.app_comp_map_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app_eq`: over a
  general coefficient ring, the proper piece of the reduction square for `Rf_!` in restriction
  form follows from the two previous statements by transposition
  (`CategoryTheory.app_comp_map_mateEquiv_app_comp_mateEquiv_app_eq_of_map`)
  and the mate description of the commutation of `Res` with `Rp_*`
  (`Etale.mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

section Generic

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}}
  (p : X ⟶ Y) (d : ℕ)
  (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
    IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))

/-- **Compatibility of pushforward squares with the restriction of scalars, from the pullback
squares**: let `γ : R₁ ⋙ r₁ ≅ r₂ ⋙ Rp_*` and `γ' : R₁ ⋙ r₁' ≅ r₂' ⋙ Rp_*` be the mates, under
an adjunction `L₁ ⊣ R₁` and `Lp^* ⊣ Rp_*` (over `Λ` and `Λ'`), of squares
`θ : r₁ ⋙ Lp^* ⟶ L₁ ⋙ r₂` and `θ' : r₁' ⋙ Lp^* ⟶ L₁ ⋙ r₂'`. If `θ` and `θ'` are intertwined by
`T₁ : r₁ ⟶ r₁' ⋙ Res`, `T₂ : r₂ ⟶ r₂' ⋙ Res` and the commutation of `Res` with `Lp^*`
(`leftDerivedUpperStarRestrictScalarsIso`), then `γ` and `γ'` are intertwined by `T₁`, `T₂` and
the commutation of `Res` with `Rp_*` (`derivedRestrictScalarsCompRightDerivedLowerStarIso`). -/
theorem app_comp_map_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app_eq
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁)
    {r₁ : C₁ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {r₂ : C₂ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {r₁' : C₁ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {r₂' : C₂ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    (T₁ : r₁ ⟶ r₁' ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ)
    (T₂ : r₂ ⟶ r₂' ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ)
    (θ : TwoSquare r₁ L₁ L((p)^*[ModuleCat.{u + 1} Λ]) r₂)
    (θ' : TwoSquare r₁' L₁ L((p)^*[ModuleCat.{u + 1} Λ']) r₂')
    (γ : R₁ ⋙ r₁ ≅ r₂ ⋙ R((p)_*[ModuleCat.{u + 1} Λ]))
    (γ' : R₁ ⋙ r₁' ≅ r₂' ⋙ R((p)_*[ModuleCat.{u + 1} Λ']))
    (h : ∀ K, L((p)^*[ModuleCat.{u + 1} Λ]).map (T₁.app K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ p).hom.app (r₁'.obj K) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (θ'.app K) =
      θ.app K ≫ T₂.app (L₁.obj K))
    (hγ : ∀ N,
      (mateEquiv a₁ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) θ).app N =
        γ.hom.app N)
    (hγ' : ∀ N,
      (mateEquiv a₁ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p) θ').app N =
        γ'.hom.app N)
    (N : C₂) :
    γ.hom.app N ≫ R((p)_*[ModuleCat.{u + 1} Λ]).map (T₂.app N) ≫
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd).hom.app (r₂'.obj N) =
      T₁.app (R₁.obj N) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map (γ'.hom.app N) := by
  have H := app_comp_map_mateEquiv_app_comp_mateEquiv_app_eq_of_map a₁
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p) T₁ T₂
    (leftDerivedUpperStarRestrictScalarsIso ρ p).hom θ θ' h N
  rw [hγ, hγ', mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso
    ρ p d hd, ← Iso.app_inv, ← Category.assoc, Iso.comp_inv_eq, Iso.app_hom] at H
  rw [H, Category.assoc]

end Generic

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section UpperStar

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `det-sp-purity-coefficient-change`, the reduction square for the pullbacks: through
the transposes `T : red_{n+1} ⟶ red_n ⋙ Res` of `β`, the comparisons
`red ⋙ Lf^* ≅ f^* ⋙ red` modulo `ℓⁿ⁺¹` and `ℓⁿ` (inverses of `etaleReductionUpperStarIso`) are
intertwined by the commutation `Res ⋙ Lf^* ≅ Lf^* ⋙ Res` of the restriction of scalars with the
derived pullbacks (`Etale.leftDerivedUpperStarRestrictScalarsIso`). -/
theorem etaleReductionUpperStarIso_restrictScalars (f : Z ⟶ Y)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) f.left).map
        ((etaleReductionTransposeNatTrans ℓ E n Y).app M) ≫
      (Etale.leftDerivedUpperStarRestrictScalarsIso (integersModPowCoeffTransition ℓ E n)
        f.left).hom.app ((etaleReduction ℓ E n Y).obj M) ≫
      (Sheaf.derivedRestrictScalars Z.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionUpperStarIso ℓ E n f).inv.app M) =
    (etaleReductionUpperStarIso ℓ E (n + 1) f).inv.app M ≫
      (etaleReductionTransposeNatTrans ℓ E n Z).app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M) := by
  have := AlgebraicGeometry.ProEtale.isIso_derivedRestrictScalarsCompComparisonLowerStarMap
    (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    Z.left
  exact map_comp_app_comp_map_eq_of_cube
    (rightDerivedComparisonBaseChange _ f.left) (rightDerivedComparisonBaseChange _ f.left)
    (derivedRestrictScalarsCompComparisonLowerStarMap _ Y.left)
    (derivedRestrictScalarsCompComparisonLowerStarMap _ Z.left)
    (Etale.leftDerivedUpperStarRestrictScalarsIso _ f.left).hom
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso _ f.left).hom
    _ _ _ _ (etaleReductionProEtaleTranspose ℓ E n Y M)
    (etaleReductionProEtaleTranspose ℓ E n Z
      ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M))
    (etaleReductionUpperStarProEtaleMap ℓ E (n + 1) f M)
    (etaleReductionUpperStarProEtaleMap ℓ E n f M)
    (etaleReductionUpperStarIso_inv_app ℓ E (n + 1) f M)
    (etaleReductionUpperStarIso_inv_app ℓ E n f M)
    (etaleReductionTransposeNatTrans_app_comp ℓ E n Y M)
    (etaleReductionTransposeNatTrans_app_comp ℓ E n Z _)
    (AlgebraicGeometry.ProEtale.map_app_comp_rightDerivedComparisonBaseChange_app_comp_map_eq _
      f.left _)
    (map_etaleReductionProEtaleTranspose_comp_eq ℓ E n f M)

end UpperStar

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

/-- The adjunction `p^* ⊣ Rp_!` on bounded constructible `𝒪_E`-complexes for a proper `p`: the
adjunction `p^* ⊣ Rp_*` transported along `Rp_! ≅ Rp_*`
(`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`). -/
noncomputable abbrev boundedConstructibleUpperStarLowerShriekAdjunction_padicIntegers :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p ⊣
      PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E p :=
  (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p).ofNatIsoRight
    (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p).symm

/-- Blueprint `det-sp-purity-coefficient-change`: for a proper `p`, the canonical comparison
`Rp_! ⋙ red ≅ red ⋙ Rp_!` (`etaleReductionLowerShriekIso`) followed by `Rp_! ≅ Rp_*` is the mate,
under `p^* ⊣ Rp_!` and `Lp^* ⊣ Rp_*`, of the inverse of the pullback comparison
`p^* ⋙ red ≅ red ⋙ Lp^*` (`etaleReductionUpperStarIso`). -/
theorem mateEquiv_etaleReductionUpperStarIso_inv (m : ℕ)
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over p
    (mateEquiv (boundedConstructibleUpperStarLowerShriekAdjunction_padicIntegers ℓ E p)
      (Etale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E m)) p.left)
      (etaleReductionUpperStarIso ℓ E m p).inv).app K =
    (etaleReductionLowerShriekIso ℓ E m p ≪≫ Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ p.left)).hom.app K := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
