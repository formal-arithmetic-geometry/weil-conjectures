/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionTranspose
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionUpperStar
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekPullback
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperStarSquare

/-!
# The reduction square for the pullbacks: the pieces

Write `T : red_{n+1} ⟶ red_n ⋙ Res` for the transpose of the compatibility `β` of the derived
extension of scalars `Ψ` with the reductions
(`ProEtale.CondensedRing.etaleReductionTransposeNatTrans`)
and `ω : Res Rν_* ⟶ Rν_* Res` for the base change map of `Res` with `Rν_*`. This file (blueprint
`det-sp-purity-coefficient-change`) provides the pieces of the reduction square for the pullbacks
(`ProEtale.CondensedRing.etaleReductionUpperStarIso_restrictScalars`):

* `ProEtale.CondensedRing.etaleReductionProEtaleTranspose`: the pro-étale transpose
  `τ : Φ(red_{n+1} K) ⟶ Res Φ(red_n K)`, `Φ` of the condensed transition, with
  `T ≫ ω = Rν_*(τ)` (`ProEtale.CondensedRing.etaleReductionTransposeNatTrans_app_comp`);
* `ProEtale.CondensedRing.etaleReductionUpperStarProEtaleMap`: the pro-étale part
  `w : Lf^* Φ(red K) ⟶ Φ(red f^* K)` of the comparison of the reduction with the pullbacks, with
  `etaleReductionUpperStarIso.inv = (Lf^* Rν_* ⟶ Rν_* Lf^*) ≫ Rν_*(w)`
  (`ProEtale.CondensedRing.etaleReductionUpperStarIso_inv_app`);
* `ProEtale.CondensedRing.map_etaleReductionProEtaleTranspose_comp_eq`: the pro-étale reduction
  square, `τ` and `w` are intertwined by the commutation of `Res` with `Lf^*`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Transpose

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The pro-étale transpose of `β`: `Φ` of the condensed transition
`red_{n+1} K ⟶ Res((𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} K) ≅ Res(red_n K)`, followed by the commutation of
`Φ` with the restrictions of scalars. -/
noncomputable def etaleReductionProEtaleTranspose
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.obj
        ((boundedConstructible _).ι.obj
          ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X.left)
        (integersModPowCoeffTransition ℓ E n)).obj
        ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))) :=
  (finiteCoefficientDerivedEquivalence X.left
      (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (integersModPowTransition X.left ℓ E n)).unit.app
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
        (Mod.comap (integersModPowTransition X.left ℓ E n)).mapDerivedCategory.map
          ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom.app K)) ≫
    (finiteCoefficientDerivedEquivalenceComapIso X.left
      (PadicAlgCl.integersModPowTransition ℓ E n)).hom.app ((boundedConstructible _).ι.obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The transpose `T` of `β`, followed by the base change map `Res Rν_* ⟶ Rν_* Res`, is `Rν_*` of
the pro-étale transpose `etaleReductionProEtaleTranspose`. -/
lemma etaleReductionTransposeNatTrans_app_comp
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReductionTransposeNatTrans ℓ E n X).app K ≫
      (derivedRestrictScalarsCompComparisonLowerStarMap (integersModPowCoeffTransition ℓ E n)
        X.left).app ((finiteCoefficientDerivedEquivalence X.left
          (PadicAlgCl.integersModPow ℓ E n)).functor.obj ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))) =
    (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))])).map
      (etaleReductionProEtaleTranspose ℓ E n X K) := by
  rw [etaleReductionTransposeNatTrans_app, assoc, ← Iso.app_hom, etaleReductionExtendScalarsIso_app]
  exact unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom ℓ E n X K

end Transpose

section UpperStar

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : Z ⟶ Y)

/-- The pro-étale part `Lf^* Φ(red K) ⟶ Φ(red f^* K)` of the inverse of the comparison of the
reduction with the pullbacks (`etaleReductionUpperStarIso`): the commutations of `Φ` with the
pullbacks, of the derived pullback with bounded constructible complexes, and of the condensed
reduction with the pullbacks. -/
noncomputable def etaleReductionUpperStarProEtaleMap
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    L(ProEtale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left).obj
        ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M))) ⟶
      (finiteCoefficientDerivedEquivalence Z.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        ((boundedConstructible _).ι.obj
          ((boundedConstructibleIntegersModPowReduction Z.left ℓ E n).obj
            ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M))) :=
  (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso f.left
      (PadicAlgCl.integersModPow ℓ E n)).inv.app
      ((boundedConstructible _).ι.obj
        ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M)) ≫
    (finiteCoefficientDerivedEquivalence Z.left (PadicAlgCl.integersModPow ℓ E n)).functor.map
      ((boundedConstructibleUpperStarCompatibility _ ℓ f).inv.app
        ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M)) ≫
    (finiteCoefficientDerivedEquivalence Z.left (PadicAlgCl.integersModPow ℓ E n)).functor.map
      ((boundedConstructible _).ι.map
        ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).inv.app M))

/-- The inverse of the comparison of the reduction with the pullbacks is the base change map
`Lf^* Rν_* ⟶ Rν_* Lf^*` followed by `Rν_*` of its pro-étale part. -/
lemma etaleReductionUpperStarIso_inv_app (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReductionUpperStarIso ℓ E n f).inv.app M =
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          f.left).app
        ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M))) ≫
        (R(ν_*(Z.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).map
          (etaleReductionUpperStarProEtaleMap ℓ E n f M) := by
  simp [etaleReductionUpperStarIso, etaleReductionUpperStarProEtaleMap]

/-- Blueprint `det-sp-purity-coefficient-change`, **the pro-étale reduction square for the
pullbacks**: the pro-étale transposes `τ` (`etaleReductionProEtaleTranspose`) are intertwined by
the pro-étale parts `w` of the comparisons of the reductions with the pullbacks
(`etaleReductionUpperStarProEtaleMap`) and the commutation of `Res` with the pro-étale derived
pullbacks (`ProEtale.leftDerivedUpperStarRestrictScalarsIso`). -/
theorem map_etaleReductionProEtaleTranspose_comp_eq
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    L(ProEtale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) f.left).map
        (etaleReductionProEtaleTranspose ℓ E n Y M) ≫
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso
        (integersModPowCoeffTransition ℓ E n) f.left).hom.app
        ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
          ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj M))) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z.left)
        (integersModPowCoeffTransition ℓ E n)).map (etaleReductionUpperStarProEtaleMap ℓ E n f M) =
    etaleReductionUpperStarProEtaleMap ℓ E (n + 1) f M ≫
      etaleReductionProEtaleTranspose ℓ E n Z
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M) := by
  sorry

end UpperStar

end AlgebraicGeometry.ProEtale.CondensedRing
