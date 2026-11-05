/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1), after a suggestion of Nailin Guan (Zulip #1852)
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateLineReading
public import WeilConjectures.WeilSheaf.SmoothPurityReadingComposition
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback

/-! # The finite étale reading of the integral one-twist datum, through type synonyms

Experiment (Nailin's suggestion): every functor, object and morphism entering the generic
composition lemma `purity_reading_composition_named` is first given a NON-EXPOSED synonym (a
plain `def`, opaque to importers), each input isomorphism/equation is restated ONCE for the
synonyms (a separate small declaration, where the only definitional work is the comparison of
that single input with its synonym), and the generic lemma is then applied to the synonyms only
(purely syntactic, no unfolding). The original statement follows in this file by unfolding the
synonyms (each synonym is literally the spelling of the original statement). -/

set_option profiler true

public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)]

section Syn

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Spec (.of k))

/-- Synonym: the condensed pullback along `g` of `(𝒪_E ⧸ ℓⁿ)`-module objects. -/
noncomputable def synP :=
  CondensedRing.upperStar (Profinite.integersModPowRingObj ℓ E n) g

/-- Synonym: extension of scalars along the reduction on `Y`. -/
noncomputable def synE := Mod.extendScalars (integersModPowReduction Y ℓ E n)

/-- Synonym: integral pullback followed by reduction on `X`. -/
noncomputable def synJ :=
  CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g ⋙
    Mod.extendScalars (integersModPowReduction X ℓ E n)

/-- Synonym: the finite-coefficient comparison functor on `Z`. -/
noncomputable def synF (Z : Scheme.{u}) :=
  (finiteCoefficientModEquivalence Z (PadicAlgCl.integersModPow ℓ E n)).functor

/-- Synonym: the pro-étale pullback of `ℤ/ℓⁿ`-module sheaves along `g`. -/
noncomputable def synQ :=
  ProEtale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g

/-- Synonym: the integral Tate line on `Y`. -/
noncomputable def synM (Z : Scheme.{u}) := integralTateTwistOne Z ℓ E

/-- Synonym: the reduced integral Tate line on `X`. -/
noncomputable def synW (Z : Scheme.{u}) :=
  (Mod.extendScalars (integersModPowReduction Z ℓ E n)).obj (integralTateTwistOne Z ℓ E)

/-- Synonym: the free module on the roots of unity on `X`. -/
noncomputable def synS (Z : Scheme.{u}) :=
  (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Z)).obj
    (rootsOfUnitySheaf Z (ℓ ^ n))

/-- Synonym: the free module on the roots of unity on `Y`. -/
noncomputable def synB (Z : Scheme.{u}) :=
  (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Z)).obj
    (rootsOfUnitySheaf Z (ℓ ^ n))

/-- Synonym: the free module on the pulled-back roots of unity. -/
noncomputable def synR :=
  (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).obj
    ((ProEtale.upperStar Ab.{u + 1} g).obj (rootsOfUnitySheaf Y (ℓ ^ n)))

/-- Synonym: the étale Tate sheaf on `X`, read pro-étale. -/
noncomputable def synT (Z : Scheme.{u}) :=
  ν^*(Z)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
    (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Z)

/-- Synonym: the étale Tate sheaf on `Y`, read pro-étale. -/
noncomputable def synT₀ (Z : Scheme.{u}) :=
  ν^*(Z)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
    (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Z)

/-- Input 1 (restated): the pullback comparison `α`. -/
noncomputable def synα : synP ℓ E n g ⋙ synF ℓ E n X ≅ synF ℓ E n Y ⋙ synQ ℓ E n g :=
  upperStarFiniteCoefficientModEquivalenceIso g (PadicAlgCl.integersModPow ℓ E n)

/-- Input 2 (restated): the pull comparison `u`. -/
noncomputable def synU : synE ℓ E n ⋙ synP ℓ E n g ⟶ synJ ℓ E n g :=
  (pullIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g).inv

/-- Input 3 (restated): the reduction of the pulled-back Tate line. -/
noncomputable def synV : (synJ ℓ E n g).obj (synM ℓ E Y) ⟶ synW ℓ E n X :=
  (Mod.extendScalars (integersModPowReduction X ℓ E n)).map
    (upperStarIntegralTateTwistOneIso ℓ E g f).hom

/-- Input 4 (restated): the reduction isomorphism on `X`. -/
noncomputable def synRX : synW ℓ E n X ≅ synS ℓ E n X :=
  extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n (g ≫ f)

/-- Input 5 (restated): the reduction isomorphism on `Y`. -/
noncomputable def synRY : (synE ℓ E n).obj (synM ℓ E Y) ≅ synB ℓ E n Y :=
  extendScalarsIntegralTateTwistOneIntegersModPowIso ℓ E n f

/-- Input 6 (restated): the free-module pullback comparison. -/
noncomputable def synQ1 : (synP ℓ E n g).obj (synB ℓ E n Y) ⟶ synR ℓ E n g :=
  (freeFunctorCompUpperStarIso (Profinite.integersModPowRingObj ℓ E n) g).hom.app
    (rootsOfUnitySheaf Y (ℓ ^ n))

/-- Input 7 (restated): the pullback of roots of unity. -/
noncomputable def synQ2 : synR ℓ E n g ⟶ synS ℓ E n X :=
  (Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).map
    (upperStarRootsOfUnitySheafHom g (ℓ ^ n))

/-- Input 8 (restated): the reading of the free root line on `X`. -/
noncomputable def synBX : (synF ℓ E n X).obj (synS ℓ E n X) ≅ synT ℓ E n X :=
  purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
    X (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f))

/-- Input 9 (restated): the reading of the free root line on `Y`. -/
noncomputable def synBY : (synF ℓ E n Y).obj (synB ℓ E n Y) ≅ synT₀ ℓ E n Y :=
  purityFiniteRootTateReadingIso (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (ringChar_integersModPowCoeff ℓ E n)
    Y (isUnit_natCast_pow_of_neZero ℓ n f)

/-- Input 10 (restated): the étale Tate pullback. -/
noncomputable def synWmor : (synQ ℓ E n g).obj (synT₀ ℓ E n Y) ⟶ synT ℓ E n X :=
  (comparisonUpperStarUpperStarIso
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
      (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
    ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
      (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g)

/-- Input 11 (restated): the named reading iso on `X`. -/
noncomputable def synTX : (synF ℓ E n X).obj (synW ℓ E n X) ≅ synT ℓ E n X :=
  finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n (g ≫ f)

/-- Input 12 (restated): the named reading iso on `Y`. -/
noncomputable def synTY : (synF ℓ E n Y).obj ((synE ℓ E n).obj (synM ℓ E Y)) ≅ synT₀ ℓ E n Y :=
  finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistOneIso ℓ E n f

/-- Equation 1 (restated): the named iso on `X` factors through the free root line. -/
lemma synTX_eq :
    synTX ℓ E n g f = (synF ℓ E n X).mapIso (synRX ℓ E n g f) ≪≫ synBX ℓ E n g f :=
  (rfl)

/-- Equation 2 (restated): the named iso on `Y` factors through the free root line. -/
lemma synTY_eq :
    synTY ℓ E n f = (synF ℓ E n Y).mapIso (synRY ℓ E n f) ≪≫ synBY ℓ E n f :=
  (rfl)

/-- Equation 3 (restated): the reduction square (`hr`). -/
lemma synHred :
    (synU ℓ E n g).app (synM ℓ E Y) ≫ synV ℓ E n g f ≫ (synRX ℓ E n g f).hom =
      (synP ℓ E n g).map (synRY ℓ E n f).hom ≫ synQ1 ℓ E n g ≫ synQ2 ℓ E n g := by
  have hr := upperStarIntegralTateTwistOneIso_hom_comp_reduction ℓ E g f n
  simp only [purityTateRootPullbackIso, upperStarRootsOfUnitySheafIsoOfInvertible_hom] at hr
  exact hr

/-- Equation 4 (restated): the reading square (`hf`). -/
lemma synHread :
    (synF ℓ E n X).map (synQ1 ℓ E n g) ≫ (synF ℓ E n X).map (synQ2 ℓ E n g) ≫
        (synBX ℓ E n g f).hom =
      (synα ℓ E n g).hom.app (synB ℓ E n Y) ≫ (synQ ℓ E n g).map (synBY ℓ E n f).hom ≫
        synWmor ℓ E n g := by
  have hzero : ((ℓ ^ n : ℕ) : PadicAlgCl.integersModPow ℓ E n) = 0 :=
    (PadicAlgCl.natCast_eq_zero_integersModPow_iff ℓ E n (ℓ ^ n)).mpr dvd_rfl
  have hf := purityFiniteRootTateReadingIso_pullback
    (PadicAlgCl.integersModPow ℓ E n) (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (ringChar_integersModPowCoeff ℓ E n) hzero g
    (isUnit_natCast_pow_of_neZero ℓ n f) (isUnit_natCast_pow_of_neZero ℓ n (g ≫ f))
  exact hf

/-- The generic composition applied to the synonyms: purely syntactic. -/
theorem purity_finiteCoefficientIntegralTateOneReading_pullback_syn :
    (synF ℓ E n X).map ((synU ℓ E n g).app (synM ℓ E Y)) ≫
        (synF ℓ E n X).map (synV ℓ E n g f) ≫ (synTX ℓ E n g f).hom =
      (synα ℓ E n g).hom.app ((synE ℓ E n).obj (synM ℓ E Y)) ≫
        (synQ ℓ E n g).map (synTY ℓ E n f).hom ≫ synWmor ℓ E n g :=
  purity_reading_composition_named (synP ℓ E n g) (synF ℓ E n Y) (synF ℓ E n X) (synQ ℓ E n g)
    (synα ℓ E n g) (synE ℓ E n) (synJ ℓ E n g) (synU ℓ E n g) (synM ℓ E Y) (synV ℓ E n g f)
    (synRX ℓ E n g f) (synRY ℓ E n f) (synQ1 ℓ E n g) (synQ2 ℓ E n g) (synBX ℓ E n g f)
    (synBY ℓ E n f) (synWmor ℓ E n g) (synTX ℓ E n g f) (synTY ℓ E n f)
    (synTX_eq ℓ E n g f) (synTY_eq ℓ E n f) (synHred ℓ E n g f) (synHread ℓ E n g f)

/-- The original statement: unfold the synonyms (each is the spelling of the statement). -/
theorem purity_finiteCoefficientIntegralTateOneReading_pullback_viaSyn :
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
  purity_finiteCoefficientIntegralTateOneReading_pullback_syn ℓ E n g f

end Syn

end AlgebraicGeometry.ProEtale
