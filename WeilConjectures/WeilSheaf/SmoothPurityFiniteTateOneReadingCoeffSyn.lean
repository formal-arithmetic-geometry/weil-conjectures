/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1), after a suggestion of Nailin Guan (Zulip #1864)
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateLineReading
public import WeilConjectures.WeilSheaf.SmoothPurityReadingComposition
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback

/-! # The finite étale reading of the integral one-twist datum, with NON-EXPOSED coefficient rings

Experiment (Nailin, Zulip #1864): the two coefficient-ring abbreviations
`Profinite.integersModPowRingObj ℓ E n` (`= continuousMapRingObj (integersModPow ℓ E n)`) and
`integersModPowCoeff ℓ E n` (`= ULift (integersModPow ℓ E n)`) get local NON-EXPOSED synonyms
`coeffRingObj` / `coeffType` (plain `def`s, no `@[expose]`, no `@[reducible]`: opaque to
importers), one equality lemma each, and the instances of `α = upperStarFiniteCoefficientModEquivalenceIso`,
`pullIso`, the comparison functor, the named reading isomorphisms and the two input equations are
rebuilt over the synonyms (each restatement is one small declaration, checked here where the
synonyms unfold).  The concrete instance is then re-run

* in this file (`purity_finiteCoefficientIntegralTateOneReading_pullback_coeffSyn`, synonym
  spelling) and in the original spelling (`…_pullback_viaCoeffSyn`, which has to unfold the
  synonyms and the abbreviations again);
* in the separate module `…CoeffSynInstance`, where the synonyms are opaque, so that neither the
  elaborator nor the kernel can unfold the coefficient rings.

`set_option profiler true` prints the time of each piece. -/

set_option profiler true

public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ)

/-! ### The non-exposed coefficient rings -/

/-- Non-exposed synonym of the condensed coefficient ring `(𝒪_E ⧸ ℓⁿ)̲`. -/
noncomputable def coeffRingObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.integersModPowRingObj.{u} ℓ E n

/-- The synonym is the original (usable only here). -/
lemma coeffRingObj_eq : coeffRingObj.{u} ℓ E n = Profinite.integersModPowRingObj.{u} ℓ E n :=
  (rfl)

noncomputable instance monObj_coeffRingObj : MonObj (coeffRingObj.{u} ℓ E n) :=
  inferInstanceAs (MonObj (Profinite.integersModPowRingObj.{u} ℓ E n))

instance isCommMonObj_coeffRingObj : IsCommMonObj (coeffRingObj.{u} ℓ E n) :=
  inferInstanceAs (IsCommMonObj (Profinite.integersModPowRingObj.{u} ℓ E n))

/-- Non-exposed synonym of the coefficient ring `𝒪_E ⧸ ℓⁿ` in the universe of étale sheaves. -/
def coeffType : Type (u + 1) := integersModPowCoeff.{u} ℓ E n

/-- The synonym is the original (usable only here). -/
lemma coeffType_eq : coeffType.{u} ℓ E n = integersModPowCoeff.{u} ℓ E n := (rfl)

noncomputable instance commRing_coeffType : CommRing (coeffType.{u} ℓ E n) :=
  inferInstanceAs (CommRing (integersModPowCoeff.{u} ℓ E n))

lemma ringChar_coeffType : ringChar (coeffType.{u} ℓ E n) = ℓ ^ n :=
  ringChar_integersModPowCoeff ℓ E n

instance neZero_ringChar_coeffType : NeZero (ringChar (coeffType.{u} ℓ E n)) :=
  inferInstanceAs (NeZero (ringChar (integersModPowCoeff.{u} ℓ E n)))

/-! ### The inputs of the generic composition lemma, rebuilt over the synonyms -/

variable {k : Type u} [Field k] [NeZero (ℓ : k)]

/-- The reduction `𝒪_{E,Z} ⟶ (𝒪_E ⧸ ℓⁿ)_Z`, typed with the synonym. -/
noncomputable def coeffReduction (Z : Scheme.{u}) :
    condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z ⟶
      condensedRingObj (coeffRingObj.{u} ℓ E n) Z :=
  integersModPowReduction Z ℓ E n

instance isMonHom_coeffReduction (Z : Scheme.{u}) : IsMonHom (coeffReduction ℓ E n Z) :=
  inferInstanceAs (IsMonHom (integersModPowReduction Z ℓ E n))

/-- The finite-coefficient comparison functor `Φ_Z`, typed with the synonyms. -/
noncomputable def coeffComparison (Z : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj (coeffRingObj.{u} ℓ E n) Z) ⥤
      Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) :=
  (finiteCoefficientModEquivalence Z (PadicAlgCl.integersModPow ℓ E n)).functor

section Inputs

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k))

/-- `α`, rebuilt over the synonyms. -/
noncomputable def coeffPullbackIso :
    CondensedRing.upperStar (coeffRingObj.{u} ℓ E n) g ⋙ coeffComparison ℓ E n X ≅
      coeffComparison ℓ E n Y ⋙ ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g :=
  upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n)

/-- `pullIso⁻¹`, rebuilt over the synonyms. -/
noncomputable def coeffPullInv :
    Mod.extendScalars (coeffReduction ℓ E n Y) ⋙ CondensedRing.upperStar (coeffRingObj.{u} ℓ E n) g ⟶
      CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g ⋙
        Mod.extendScalars (coeffReduction ℓ E n X) :=
  (pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv

/-- The reduction isomorphism on `Z` (`rX`/`rY`), rebuilt over the synonyms. -/
noncomputable def coeffReductionIso {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) :
    (Mod.extendScalars (coeffReduction ℓ E n Z)).obj (integralTateTwistOne Z ℓ E) ≅
      (Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) Z)).obj
        (rootsOfUnitySheaf Z (ℓ ^ n)) :=
  extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n h

/-- The reading of the free root line on `Z` (`bX`/`bY`), rebuilt over the synonyms. -/
noncomputable def coeffRootReadingIso {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) :
    (coeffComparison ℓ E n Z).obj
        ((Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) Z)).obj
          (rootsOfUnitySheaf Z (ℓ ^ n))) ≅
      ν^*(Z)[ModuleCat.{u + 1} (coeffType.{u} ℓ E n)].obj
        (Etale.tateSheaf (coeffType.{u} ℓ E n) Z) :=
  purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
    Z (isUnit_natCast_pow_of_neZero ℓ n h)

/-- The named reading isomorphism on `Z` (`tX`/`tY`), rebuilt over the synonyms. -/
noncomputable def coeffTateReadingIso {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) :
    (coeffComparison ℓ E n Z).obj
        ((Mod.extendScalars (coeffReduction ℓ E n Z)).obj (integralTateTwistOne Z ℓ E)) ≅
      ν^*(Z)[ModuleCat.{u + 1} (coeffType.{u} ℓ E n)].obj
        (Etale.tateSheaf (coeffType.{u} ℓ E n) Z) :=
  finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n h

/-- `htX`/`htY`, rebuilt over the synonyms (no new unfolding: the original factorization). -/
lemma coeffTateReadingIso_eq {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) :
    coeffTateReadingIso ℓ E n h =
      (coeffComparison ℓ E n Z).mapIso (coeffReductionIso ℓ E n h) ≪≫
        coeffRootReadingIso ℓ E n h :=
  purity_finiteCoefficientIntegralTateOneReading_eq ℓ E n h

/-- The étale Tate pullback `w`, written with the synonym (no restatement needed: the
coefficient type is a parameter). -/
noncomputable def coeffTatePull :
    (ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g).obj
        (ν^*(Y)[ModuleCat.{u + 1} (coeffType.{u} ℓ E n)].obj
          (Etale.tateSheaf (coeffType.{u} ℓ E n) Y)) ⟶
      ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} ℓ E n)].obj
        (Etale.tateSheaf (coeffType.{u} ℓ E n) X) :=
  (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g).hom.app
      (Etale.tateSheaf (coeffType.{u} ℓ E n) Y) ≫
    ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} ℓ E n)].map
      (Etale.upperStarTateSheafToTateSheaf (coeffType.{u} ℓ E n) g)

/-- The reduction square `hr`, restated over the synonyms. -/
lemma coeffHred :
    (coeffPullInv ℓ E n g).app (integralTateTwistOne Y ℓ E) ≫
        (Mod.extendScalars (coeffReduction ℓ E n X)).map
          (upperStarIntegralTateTwistOneIso ℓ E g f).hom ≫
        (coeffReductionIso ℓ E n (g ≫ f)).hom =
      (CondensedRing.upperStar (coeffRingObj.{u} ℓ E n) g).map (coeffReductionIso ℓ E n f).hom ≫
        (freeFunctorCompUpperStarIso (coeffRingObj.{u} ℓ E n) g).hom.app
          (rootsOfUnitySheaf Y (ℓ ^ n)) ≫
        (Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) X)).map
          (upperStarRootsOfUnitySheafHom g (ℓ ^ n)) := by
  have hr := upperStarIntegralTateTwistOneIso_hom_comp_reduction ℓ E g f n
  simp only [purityTateRootPullbackIso, upperStarRootsOfUnitySheafIsoOfInvertible_hom] at hr
  exact hr

/-- The reading square `hf`, restated over the synonyms. -/
lemma coeffHread :
    (coeffComparison ℓ E n X).map
          ((freeFunctorCompUpperStarIso (coeffRingObj.{u} ℓ E n) g).hom.app
            (rootsOfUnitySheaf Y (ℓ ^ n))) ≫
        (coeffComparison ℓ E n X).map
          ((Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) X)).map
            (upperStarRootsOfUnitySheafHom g (ℓ ^ n))) ≫
        (coeffRootReadingIso ℓ E n (g ≫ f)).hom =
      (coeffPullbackIso ℓ E n g).hom.app
          ((Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) Y)).obj
            (rootsOfUnitySheaf Y (ℓ ^ n))) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g).map
          (coeffRootReadingIso ℓ E n f).hom ≫
        coeffTatePull ℓ E n g := by
  have hzero : ((ℓ ^ n : ℕ) : PadicAlgCl.integersModPow ℓ E n) = 0 :=
    (PadicAlgCl.natCast_eq_zero_integersModPow_iff ℓ E n (ℓ ^ n)).mpr dvd_rfl
  have hf := purityFiniteRootTateReadingIso_pullback
    (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (ringChar_integersModPowCoeff ℓ E n) hzero g
    (isUnit_natCast_pow_of_neZero ℓ n f) (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f))
  exact hf

/-! ### The instance, in the synonym spelling (same module: the synonyms could still unfold) -/

/-- The concrete instance over the synonyms. -/
theorem purity_finiteCoefficientIntegralTateOneReading_pullback_coeffSyn :
    (coeffComparison ℓ E n X).map ((coeffPullInv ℓ E n g).app (integralTateTwistOne Y ℓ E)) ≫
        (coeffComparison ℓ E n X).map
          ((Mod.extendScalars (coeffReduction ℓ E n X)).map
            (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
        (coeffTateReadingIso ℓ E n (g ≫ f)).hom =
      (coeffPullbackIso ℓ E n g).hom.app
          ((Mod.extendScalars (coeffReduction ℓ E n Y)).obj (integralTateTwistOne Y ℓ E)) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g).map
          (coeffTateReadingIso ℓ E n f).hom ≫
        coeffTatePull ℓ E n g :=
  purity_reading_composition_named (CondensedRing.upperStar (coeffRingObj.{u} ℓ E n) g)
    (coeffComparison ℓ E n Y) (coeffComparison ℓ E n X)
    (ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g) (coeffPullbackIso ℓ E n g)
    (Mod.extendScalars (coeffReduction ℓ E n Y))
    (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g ⋙
      Mod.extendScalars (coeffReduction ℓ E n X))
    (coeffPullInv ℓ E n g) (integralTateTwistOne Y ℓ E)
    ((Mod.extendScalars (coeffReduction ℓ E n X)).map
      (upperStarIntegralTateTwistOneIso ℓ E g f).hom)
    (coeffReductionIso ℓ E n (g ≫ f)) (coeffReductionIso ℓ E n f)
    ((freeFunctorCompUpperStarIso (coeffRingObj.{u} ℓ E n) g).hom.app
      (rootsOfUnitySheaf Y (ℓ ^ n)))
    ((Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) X)).map
      (upperStarRootsOfUnitySheafHom g (ℓ ^ n)))
    (coeffRootReadingIso ℓ E n (g ≫ f)) (coeffRootReadingIso ℓ E n f) (coeffTatePull ℓ E n g)
    (coeffTateReadingIso ℓ E n (g ≫ f)) (coeffTateReadingIso ℓ E n f)
    (coeffTateReadingIso_eq ℓ E n (g ≫ f)) (coeffTateReadingIso_eq ℓ E n f)
    (coeffHred ℓ E n g f) (coeffHread ℓ E n g f)

/-- The original statement, by unfolding the synonyms (this is the cost that disappears if the
originals become non-exposed and all users are stated in the synonym spelling). -/
theorem purity_finiteCoefficientIntegralTateOneReading_pullback_viaCoeffSyn :
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv.app
            (integralTateTwistOne Y ℓ E)) ≫
        (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((Mod.extendScalars (integersModPowReduction X ℓ E n)).map
            (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
        (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso
          ℓ E n (g ≫ f)).hom =
      (upperStarFiniteCoefficientModEquivalenceIso g
        (PadicAlgCl.integersModPow ℓ E n)).hom.app
          ((Mod.extendScalars (integersModPowReduction Y ℓ E n)).obj
            (integralTateTwistOne Y ℓ E)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f).hom ≫
        (comparisonUpperStarUpperStarIso
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
            (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g) :=
  purity_finiteCoefficientIntegralTateOneReading_pullback_coeffSyn ℓ E n g f

end Inputs

end AlgebraicGeometry.ProEtale
