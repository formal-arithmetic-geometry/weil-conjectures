/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionLowerShriekOpen
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekMate

/-!
# The open-immersion piece of the reduction square for `Rj_!`, transposed to `j^*`

Write `Ψ` for the derived extension of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site,
`β : Ψ(red_{n+1} K) ≅ red_n K` for its compatibility with the reductions and
`T : red_{n+1} ⟶ Res ∘ red_n` for the transpose of `β` under `Ψ ⊣ Res`
(`ProEtale.CondensedRing.etaleReductionTransposeNatTrans`). For an open immersion `j : U ⟶ X`,
the canonical comparison `Rj_! ⋙ red ≅ red ⋙ D(j_!)` is, under the adjunctions `Rj_! ⊣ Rj^!` and
`D(j_!) ⊣ D(j^*)`, the transpose of the comparison
`j^! ⋙ red ≅ j^* ⋙ red ≅ red ⋙ D(j^*)`
(`ProEtale.CondensedRing.etaleReductionUpperStarIsoOfIsOpenImmersion`,
`ProEtale.CondensedRing.mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_app`).
This file (blueprint `det-sp-purity-coefficient-change`) states the compatibility of the latter
with `T` and the mate `D(j^*) ⋙ Res ⟶ Res ⋙ D(j^*)` of the commutation of `Res` with `D(j_!)`
(`ProEtale.CondensedRing.etaleReductionUpperStarIsoOfIsOpenImmersion_restrictScalars`), from which
the compatibility for `Rj_!` follows by
`CategoryTheory.map_app_comp_app_comp_map_app_eq_of_mateEquiv`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- The transpose `red_{n+1} ⟶ red_n ⋙ Res` of `β : red_{n+1} ⋙ Ψ ≅ red_n` under `Ψ ⊣ Res`. -/
noncomputable def etaleReductionTransposeNatTrans (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    etaleReduction ℓ E (n + 1) X ⟶ etaleReduction ℓ E n X ⋙
      Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n) :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Etale.derivedExtendScalarsAdjunction
      (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) X.left).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleReductionExtendScalarsIso ℓ E n X).hom _

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The components of `etaleReductionTransposeNatTrans`. -/
lemma etaleReductionTransposeNatTrans_app (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReductionTransposeNatTrans ℓ E n X).app K =
      (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n) X.left).unit.app _ ≫
        (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
          (integersModPowCoeffTransition ℓ E n)).map
            ((etaleReductionExtendScalarsIso ℓ E n X).hom.app K) := by
  simp [etaleReductionTransposeNatTrans]

variable {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- For an open immersion `j`, the comparison `j^! ⋙ red_U ≅ red_X ⋙ D(j^*)`: the
identification `j^! ≅ j^*` on the condensed side, followed by the commutation of the reduction
with the pullbacks (`etaleReductionUpperStarIso`) and `Lj^* ≅ D(j^*)`. -/
noncomputable def etaleReductionUpperStarIsoOfIsOpenImmersion (m : ℕ) :
    have := HasCompactification.of_over j
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j ⋙ etaleReduction ℓ E m U ≅
      etaleReduction ℓ E m X ⋙
        (Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E m))
          j.left).mapDerivedCategory :=
  have := HasCompactification.of_over j
  Functor.isoWhiskerRight (boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j) _ ≪≫
    etaleReductionUpperStarIso ℓ E m j ≪≫
    Functor.isoWhiskerLeft _ (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ j.left)

/-- The transpose of `Rj_! ⋙ red_X ≅ red_U ⋙ Rj_! ≅ red_U ⋙ D(j_!)` under the adjunctions
`Rj_! ⊣ j^!` and `D(j_!) ⊣ D(j^*)` is `etaleReductionUpperStarIsoOfIsOpenImmersion`. -/
lemma mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_app (m : ℕ)
    (N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over j
    have := quasiCompact_left_of_over j
    (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E m)) j.left)
      ((TwoSquare.mk _ _ _ _
        (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E m j).inv).whiskerRight
        (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left).inv)).app N =
      (etaleReductionUpperStarIsoOfIsOpenImmersion ℓ E j m).hom.app N := by
  intro _ _
  rw [mateEquiv_whiskerRight_inv_app, mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion]
  simp only [etaleReductionUpperShriekIsoOfIsOpenImmersion,
    etaleReductionUpperStarIsoOfIsOpenImmersion,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]

/-- `mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_app`, for the composite
isomorphism `Rj_! ⋙ red_X ≅ red_U ⋙ D(j_!)`. -/
lemma mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_inv_app (m : ℕ)
    (N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over j
    have := quasiCompact_left_of_over j
    (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j)
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E m)) j.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E m j ≪≫
        Functor.isoWhiskerLeft _
          (Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion _ j.left)).inv)).app N =
      (etaleReductionUpperStarIsoOfIsOpenImmersion ℓ E j m).hom.app N :=
  mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion_trans_app ℓ E j m N

/-- Blueprint `det-sp-purity-coefficient-change`, the open-immersion piece transposed to `j^*`:
through the transposes `T : red_{n+1} ⟶ red_n ⋙ Res` of `β`, the comparisons
`j^! ⋙ red ≅ red ⋙ D(j^*)` modulo `ℓⁿ⁺¹` and `ℓⁿ`
(`etaleReductionUpperStarIsoOfIsOpenImmersion`) are intertwined by the mate
`D(j^*) ⋙ Res ⟶ Res ⋙ D(j^*)` of the commutation of `Res` with `D(j_!)`
(`Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`). -/
theorem etaleReductionUpperStarIsoOfIsOpenImmersion_restrictScalars
    (N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over j
    (etaleReductionTransposeNatTrans ℓ E n U).app
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j).obj N) ≫
      (Sheaf.derivedRestrictScalars U.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionUpperStarIsoOfIsOpenImmersion ℓ E j n).hom.app N) ≫
      (mateEquiv (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) j.left)
        (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) j.left)
        (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso
          (integersModPowCoeffTransition ℓ E n) j.left).hom).app
        ((etaleReduction ℓ E n X).obj N) =
    (etaleReductionUpperStarIsoOfIsOpenImmersion ℓ E j (n + 1)).hom.app N ≫
      (Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
        j.left).mapDerivedCategory.map ((etaleReductionTransposeNatTrans ℓ E n X).app N) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
