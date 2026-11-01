/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionLowerShriekComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionLowerShriekOpen
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekPullback
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekUpperStar

/-!
# The reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` and the comparisons for `Rf_!`

Write `Ψ` for the derived extension of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site,
`β : Ψ(red_{n+1} K) ≅ red_n K` for its compatibility with the reductions
(`ProEtale.CondensedRing.etaleReductionExtendScalarsIso`) and, for `f : X ⟶ Y`,
`β_f : Ψ Rf_! ⟶ Rf_! Ψ` for the transpose of the commutation of the restriction of scalars with
`Rf_!` (`Etale.derivedExtendScalarsLowerShriekMap`). This file (blueprint
`det-sp-purity-coefficient-change`) reduces the compatibility of `β` and `β_f` with the canonical
comparisons `Rf_! ⋙ red_Y ≅ red_X ⋙ Rf_!` of a compactification
(`etaleReductionLowerShriekIsoOfCompactification`) to the two pieces of the compactification:

* `reductionSquareCompatible_etaleReductionLowerShriekIsoOfIsOpenImmersion`: the open immersion;
* `reductionSquareCompatible_etaleReductionLowerShriekIso`: the proper morphism, by transposing the
  reduction square for the pullbacks along `p^* ⊣ Rp_!` and `Lp^* ⊣ Rp_*`
  (`Etale.reductionSquareCompatible_derivedRestrictScalarsCompRightDerivedLowerStarIso`);
* `reductionSquareCompatible_etaleReductionLowerShriekIsoOfCompactification`: the assembly, by the
  stability under composition (`Etale.ReductionSquareCompatible.comp`) and the compatibility of the
  composition isomorphisms of `R_!` with the restriction of scalars
  (`Etale.coeffCompatible_rightDerivedLowerShriekCompIsoOfEq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

open scoped CategoryTheory.Functor

/-- **Compatibility of the pushforward reduction squares with `β`, from the pullback squares**:
let `γA : Rp_! ⋙ rA_Y ≅ rA_X ⋙ Rp_*` and `γB : Rp_! ⋙ rB_Y ≅ rB_X ⋙ Rp_*` be the mates, under an
adjunction `G ⊣ F` and `Lp^* ⊣ Rp_*` (over `Λ` and `Λ'`), of squares
`θ : rA_Y ⋙ Lp^* ⟶ G ⋙ rA_X` and `θ' : rB_Y ⋙ Lp^* ⟶ G ⋙ rB_X`. If `θ` and `θ'` are intertwined
by the transposes `rA ⟶ rB ⋙ Res` of `β` and the commutation of `Res` with `Lp^*`
(`leftDerivedUpperStarRestrictScalarsIso`), then `γA` and `γB` are compatible with `β` through
the commutation of `Res` with `Rp_*` (`derivedRestrictScalarsCompRightDerivedLowerStarIso`). -/
theorem reductionSquareCompatible_derivedRestrictScalarsCompRightDerivedLowerStarIso
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}}
    (p : X ⟶ Y) (d : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    {K₁ K₂ : Type*} [Category K₁] [Category K₂] {F : K₁ ⥤ K₂} {G : K₂ ⥤ K₁} (a : G ⊣ F)
    {rA₁ : K₁ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {rA₂ : K₂ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {rB₁ : K₁ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {rB₂ : K₂ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {Ψ₁ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {Ψ₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    (adj₁ : Ψ₁ ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ)
    (adj₂ : Ψ₂ ⊣ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ)
    (β₁ : rA₁ ⋙ Ψ₁ ≅ rB₁) (β₂ : rA₂ ⋙ Ψ₂ ≅ rB₂)
    (θ : TwoSquare rA₂ G L((p)^*[ModuleCat.{u + 1} Λ]) rA₁)
    (θ' : TwoSquare rB₂ G L((p)^*[ModuleCat.{u + 1} Λ']) rB₁)
    (γA : F ⋙ rA₂ ≅ rA₁ ⋙ R((p)_*[ModuleCat.{u + 1} Λ]))
    (γB : F ⋙ rB₂ ≅ rB₁ ⋙ R((p)_*[ModuleCat.{u + 1} Λ']))
    (h : ∀ M, L((p)^*[ModuleCat.{u + 1} Λ]).map
        (adj₂.unit.app (rA₂.obj M) ≫
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map (β₂.hom.app M)) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ p).hom.app (rB₂.obj M) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (θ'.app M) =
      θ.app M ≫ adj₁.unit.app (rA₁.obj (G.obj M)) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (β₁.hom.app (G.obj M)))
    (hγA : ∀ N,
      (mateEquiv a (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) θ).app N =
        γA.hom.app N)
    (hγB : ∀ N,
      (mateEquiv a (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p) θ').app N =
        γB.hom.app N) :
    ReductionSquareCompatible adj₁ adj₂ β₁ β₂
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd) γA γB := by
  let T₁ : rA₂ ⟶ rB₂ ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ :=
    (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ adj₂.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight β₂.hom _
  let T₂ : rA₁ ⟶ rB₁ ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ :=
    (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ adj₁.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight β₁.hom _
  have hT₁ (M : K₂) : T₁.app M = adj₂.unit.app (rA₂.obj M) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map (β₂.hom.app M) := by
    simp [T₁]
  have hT₂ (N : K₁) : T₂.app N = adj₁.unit.app (rA₁.obj N) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (β₁.hom.app N) := by
    simp [T₂]
  refine (reductionSquareCompatible_iff_unit _ _ _ _ _ _ _).2 fun N ↦ ?_
  have H := app_comp_map_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app_eq ρ p d
    hd a T₁ T₂ θ θ' γA γB (fun M ↦ by rw [hT₁, hT₂]; exact h M) hγA hγB N
  rw [hT₁, hT₂] at H
  rw [Category.assoc, H, Category.assoc]

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- The comparisons `γ_{n+1} : Rf_! ⋙ red_{n+1} ≅ red_{n+1} ⋙ Rf_!` and
`γ_n : Rf_! ⋙ red_n ≅ red_n ⋙ Rf_!` are *compatible with the reduction*
`β : Ψ(red_{n+1} -) ≅ red_n -` if `Ψ(γ_{n+1} K) ≫ β_f(red_{n+1} K) ≫ Rf_!(β K) = β(Rf_! K) ≫ γ_n K`,
where `β_f : Ψ Rf_! ⟶ Rf_! Ψ` is `Etale.derivedExtendScalarsLowerShriekMap`. -/
abbrev EtaleReductionLowerShriekCompatible {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) [HasCompactification f.left] [CompactSpace Y.left]
    (γ₁ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        etaleReduction ℓ E (n + 1) Y ≅ etaleReduction ℓ E (n + 1) X ⋙
          Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
            f.left)
    (γ₀ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        etaleReduction ℓ E n Y ≅ etaleReduction ℓ E n X ⋙
          Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
            f.left) : Prop :=
  Etale.ReductionSquareCompatible
    (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) X.left)
    (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) Y.left)
    (etaleReductionExtendScalarsIso ℓ E n X) (etaleReductionExtendScalarsIso ℓ E n Y)
    (Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso
      (integersModPowCoeffTransition ℓ E n) f.left) γ₁ γ₀

/-- The transpose `red_{n+1} K ⟶ Res(red_n K)` of `β : Ψ(red_{n+1} K) ≅ red_n K` under `Ψ ⊣ Res`
(computed by `unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom`). -/
noncomputable abbrev etaleReductionTranspose (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReduction ℓ E (n + 1) X).obj K ⟶
      (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).obj ((etaleReduction ℓ E n X).obj K) :=
  (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) X.left).unit.app _ ≫
    (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
      (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionExtendScalarsIso ℓ E n X).hom.app K)

/-- Blueprint `det-sp-purity-coefficient-change`, the open-immersion piece in restriction form:
through the transposes `T : red_{n+1} ⟶ Res red_n` of `β`, the comparisons
`Rj_! ⋙ red ≅ red ⋙ D(j_!)` modulo `ℓⁿ⁺¹` and `ℓⁿ` are intertwined by the commutation of `Res`
with `D(j_!)`. -/
theorem etaleReductionLowerShriekIsoOfIsOpenImmersion_extensionByZero_restrictScalars
    {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left]
    (K : Dᵇc(U.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over j
    have := quasiCompact_left_of_over j
    (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E (n + 1) j ≪≫ Functor.isoWhiskerLeft _
        (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).hom.app K ≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
        j.left).mapDerivedCategory.map (etaleReductionTranspose ℓ E n U K) ≫
      (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso
        (integersModPowCoeffTransition ℓ E n) j.left).hom.app ((etaleReduction ℓ E n U).obj K) =
    etaleReductionTranspose ℓ E n X
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j).obj K) ≫
      (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j ≪≫ Functor.isoWhiskerLeft _
          (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).hom.app K) := by
  intro _ _
  have h := map_app_comp_app_comp_map_app_eq_of_mateEquiv
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) j.left)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) j.left)
    (etaleReductionTransposeNatTrans ℓ E n U) (etaleReductionTransposeNatTrans ℓ E n X)
    (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso
      (integersModPowCoeffTransition ℓ E n) j.left).hom
    (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E (n + 1) j ≪≫
      Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).inv)
    (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j ≪≫
      Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).inv)
    (fun N ↦ by
      rw [mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_inv_app,
        mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_inv_app]
      exact etaleReductionUpperStarIsoOfIsOpenImmersion_restrictScalars ℓ E n j N) K
  rw [etaleReductionTransposeNatTrans_app, etaleReductionTransposeNatTrans_app] at h
  have h' : (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) j.left).mapDerivedCategory.map
        (etaleReductionTranspose ℓ E n U K) ≫
      (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso
        (integersModPowCoeffTransition ℓ E n) j.left).hom.app ((etaleReduction ℓ E n U).obj K) ≫
      (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j ≪≫ Functor.isoWhiskerLeft _
          (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).inv.app K) =
    (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E (n + 1) j ≪≫ Functor.isoWhiskerLeft _
        (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).inv.app K ≫
      etaleReductionTranspose ℓ E n X
        ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j).obj K) := h
  rw [← cancel_epi ((etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E (n + 1) j ≪≫
    Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).inv.app K),
    Iso.inv_hom_id_app_assoc, ← Category.assoc, ← h', Category.assoc, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Blueprint `det-sp-purity-coefficient-change`, the open-immersion piece with `Rj_!` replaced by
the extension by zero `D(j_!)`: for an open immersion `j`, the canonical comparisons
`Rj_! ⋙ red ≅ red ⋙ Rj_!` (`etaleReductionLowerShriekIsoOfIsOpenImmersion`) followed by
`Rj_! ≅ D(j_!)` on the étale side, modulo `ℓⁿ⁺¹` and `ℓⁿ`, are compatible with the reduction `β`
through the commutation of the restriction of scalars with `D(j_!)`
(`Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`). -/
theorem reductionSquareCompatible_etaleReductionLowerShriekIsoOfIsOpenImmersion_extensionByZero
    {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    have := HasCompactification.of_over j
    have := quasiCompact_left_of_over j
    Etale.ReductionSquareCompatible
      (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) U.left)
      (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) X.left)
      (etaleReductionExtendScalarsIso ℓ E n U) (etaleReductionExtendScalarsIso ℓ E n X)
      (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso
        (integersModPowCoeffTransition ℓ E n) j.left)
      (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E (n + 1) j ≪≫ Functor.isoWhiskerLeft _
        (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left))
      (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j ≪≫ Functor.isoWhiskerLeft _
        (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)) := by
  intro _ _
  exact (Etale.reductionSquareCompatible_iff_unit _ _ _ _ _ _ _).2
    (fun K ↦ etaleReductionLowerShriekIsoOfIsOpenImmersion_extensionByZero_restrictScalars ℓ E n
      j K)

/-- Blueprint `det-sp-purity-coefficient-change`, the open-immersion piece: for an open immersion
`j`, the canonical comparisons `Rj_! ⋙ red ≅ red ⋙ Rj_!`
(`etaleReductionLowerShriekIsoOfIsOpenImmersion`) modulo `ℓⁿ⁺¹` and `ℓⁿ` are compatible with the
reduction `β`. -/
theorem reductionSquareCompatible_etaleReductionLowerShriekIsoOfIsOpenImmersion
    {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] [CompactSpace X.left] :
    have := HasCompactification.of_over j
    EtaleReductionLowerShriekCompatible ℓ E n j
      (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E (n + 1) j)
      (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j) :=
  have := HasCompactification.of_over j
  have := quasiCompact_left_of_over j
  Etale.ReductionSquareCompatible.of_trans_isoWhiskerLeft
    (reductionSquareCompatible_etaleReductionLowerShriekIsoOfIsOpenImmersion_extensionByZero ℓ E n
      j)
    (Etale.coeffCompatible_rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left).inv

/-- Blueprint `det-sp-purity-coefficient-change`, the proper piece with `Rp_!` replaced by `Rp_*`:
for a proper `p`, the canonical comparisons `Rp_! ⋙ red ≅ red ⋙ Rp_!`
(`etaleReductionLowerShriekIso`) followed by `Rp_! ≅ Rp_*` on the étale side, modulo `ℓⁿ⁺¹` and
`ℓⁿ`, are compatible with the reduction `β` through the commutation of the restriction of scalars
with `Rp_*` (`Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso`). -/
theorem reductionSquareCompatible_etaleReductionLowerShriekIso_lowerStar
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] [CompactSpace Y.left] (d : ℕ)
    (hd : ∀ (F : Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))) (q : ℕ), d < q →
      IsZero ((((Etale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
        p.left)).rightDerived q).obj F)) :
    have := HasCompactification.of_over p
    Etale.ReductionSquareCompatible
      (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) X.left)
      (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left)
      (etaleReductionExtendScalarsIso ℓ E n X) (etaleReductionExtendScalarsIso ℓ E n Y)
      (Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso
        (integersModPowCoeffTransition ℓ E n) p.left d hd)
      (etaleReductionLowerShriekIso ℓ E (n + 1) p ≪≫ Functor.isoWhiskerLeft _
        (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ p.left))
      (etaleReductionLowerShriekIso ℓ E n p ≪≫ Functor.isoWhiskerLeft _
        (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ p.left)) :=
  have := HasCompactification.of_over p
  Etale.reductionSquareCompatible_derivedRestrictScalarsCompRightDerivedLowerStarIso _ p.left d hd
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicIntegers ℓ E p) _ _ _ _
    (etaleReductionUpperStarIso ℓ E (n + 1) p).inv (etaleReductionUpperStarIso ℓ E n p).inv _ _
    (fun M ↦ by
      have h := etaleReductionUpperStarIso_restrictScalars ℓ E n p M
      rw [etaleReductionTransposeNatTrans_app, etaleReductionTransposeNatTrans_app] at h
      exact h)
    (mateEquiv_etaleReductionUpperStarIso_inv ℓ E p (n + 1))
    (mateEquiv_etaleReductionUpperStarIso_inv ℓ E p n)


/-- Blueprint `det-sp-purity-coefficient-change`, the proper piece: for a proper `p`, the canonical
comparisons `Rp_! ⋙ red ≅ red ⋙ Rp_!` (`etaleReductionLowerShriekIso`) modulo `ℓⁿ⁺¹` and `ℓⁿ` are
compatible with the reduction `β`. -/
theorem reductionSquareCompatible_etaleReductionLowerShriekIso
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] [CompactSpace Y.left] :
    have := HasCompactification.of_over p
    EtaleReductionLowerShriekCompatible ℓ E n p
      (etaleReductionLowerShriekIso ℓ E (n + 1) p) (etaleReductionLowerShriekIso ℓ E n p) := by
  intro
  obtain ⟨d, hd⟩ := Etale.exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace
    (integersModPowCoeff.{u} ℓ E (n + 1)) isAddTorsion_of_finite p.left
  exact Etale.ReductionSquareCompatible.of_trans_isoWhiskerLeft
    (reductionSquareCompatible_etaleReductionLowerShriekIso_lowerStar ℓ E n p d hd)
    (Etale.coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar _ p.left d hd).inv

section Comp

variable {X Y S : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  {f : X ⟶ Y} {g : Y ⟶ S} {h : X ⟶ S}
  [HasCompactification f.left] [HasCompactification g.left] [HasCompactification h.left]

/-- The components of the inverse of the stacked comparison `etaleReductionLowerShriekIsoOfComp`. -/
lemma etaleReductionLowerShriekIsoOfComp_inv_app (w : f ≫ g = h)
    (γf : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)
    (γg : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          g.left)
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := quasiCompact_left_of_over h
    (etaleReductionLowerShriekIsoOfComp ℓ E n w γf γg).inv.app K =
      (Etale.rightDerivedLowerShriekCompIsoOfEq (integersModPowCoeff.{u} ℓ E n) f.left g.left
          h.left (by rw [← w]; rfl)).hom.app ((etaleReduction ℓ E n X).obj K) ≫
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          g.left).map (γf.inv.app K) ≫
        γg.inv.app ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f).obj K) ≫
        (etaleReduction ℓ E n S).map
          ((boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers ℓ E w).inv.app K) := by
  simp [etaleReductionLowerShriekIsoOfComp, etaleReductionLowerShriekSquareOfComp]

variable [CompactSpace Y.left] [CompactSpace S.left]

/-- **Compatibility with the reduction is stable under composition**: if the comparisons for `f`
and `g` are compatible with `β`, so are the stacked comparisons
`etaleReductionLowerShriekIsoOfComp` for `f ≫ g = h`. -/
theorem EtaleReductionLowerShriekCompatible.comp (w : f ≫ g = h)
    {γf₁ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        etaleReduction ℓ E (n + 1) Y ≅ etaleReduction ℓ E (n + 1) X ⋙
          Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
            f.left}
    {γf₀ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙ etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left}
    {γg₁ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙
        etaleReduction ℓ E (n + 1) S ≅ etaleReduction ℓ E (n + 1) Y ⋙
          Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
            g.left}
    {γg₀ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E g ⋙ etaleReduction ℓ E n S ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g.left}
    (hf : EtaleReductionLowerShriekCompatible ℓ E n f γf₁ γf₀)
    (hg : EtaleReductionLowerShriekCompatible ℓ E n g γg₁ γg₀) :
    EtaleReductionLowerShriekCompatible ℓ E n h
      (etaleReductionLowerShriekIsoOfComp ℓ E (n + 1) w γf₁ γg₁)
      (etaleReductionLowerShriekIsoOfComp ℓ E n w γf₀ γg₀) := by
  have := quasiCompact_left_of_over h
  exact Etale.ReductionSquareCompatible.comp hf hg
    (boundedConstructibleLowerShriekCompIsoOfEq_padicIntegers ℓ E w)
    (Etale.rightDerivedLowerShriekCompIsoOfEq _ f.left g.left h.left (by rw [← w]; rfl))
    (Etale.rightDerivedLowerShriekCompIsoOfEq _ f.left g.left h.left (by rw [← w]; rfl))
    (Etale.coeffCompatible_rightDerivedLowerShriekCompIsoOfEq _ f.left g.left h.left
      (by rw [← w]; rfl))
    (etaleReductionLowerShriekIsoOfComp_inv_app ℓ E (n + 1) w γf₁ γg₁)
    (etaleReductionLowerShriekIsoOfComp_inv_app ℓ E n w γf₀ γg₀)

end Comp

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} [HasCompactification f.left] [CompactSpace Y.left]

/-- Blueprint `det-sp-purity-coefficient-change`: **the canonical comparisons
`Rf_! ⋙ red ≅ red ⋙ Rf_!` of a compactification are compatible with the reduction `β`**, by
composition of the open-immersion and proper pieces. -/
theorem reductionSquareCompatible_etaleReductionLowerShriekIsoOfCompactification
    (c : Compactification f.left) :
    EtaleReductionLowerShriekCompatible ℓ E n f
      (etaleReductionLowerShriekIsoOfCompactification ℓ E (n + 1) c)
      (etaleReductionLowerShriekIsoOfCompactification ℓ E n c) := by
  have := HasCompactification.of_over c.overI
  have := HasCompactification.of_over c.overG
  have : CompactSpace c.overObj.left := QuasiCompact.compactSpace_of_compactSpace c.g
  exact (reductionSquareCompatible_etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n
    c.overI).comp ℓ E n c.overI_overG
    (reductionSquareCompatible_etaleReductionLowerShriekIso ℓ E n c.overG)

end AlgebraicGeometry.ProEtale.CondensedRing
