/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.IntegralResidueTensorPresentation
public import Sheaf.Paper.IntegralResidueOrdinaryMonoidal

/-! # Ordinary pullback data and the derived residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Remark 6.8.15.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Pullback identifies the restricted residue regular coefficient in degree zero.
The isomorphism is constructed using exact pullback and its ordinary unit comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation) -/
@[irreducible] noncomputable def residueExchangeCoefficientPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y) ≅ residueExchangeCoefficient ℓ E X := by
  let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
  let P := Mod.regular (condensedRingObj A Y)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  letI := residueOrdinaryUpperStarMonoidal A f
  let e : (f)^*⟦integralCoeff ℓ E⟧.obj (SY.obj P) ≅
      SX.obj (Mod.regular (condensedRingObj A X)) :=
    (comapUpperStarIso (integralReductionMap ℓ E) f).symm.app P ≪≫
      SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
  unfold residueExchangeUpperStar
  exact ((f)^*⟦integralCoeff ℓ E⟧.singleFunctorCompLeftDerivedFunctorIso).app (SY.obj P) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- The tensor presentation on X, with its coefficient identified with pullback from Y.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: def-weil-pbc-integral-residue-tensor-pull-presentation) -/
@[irreducible] noncomputable def residueExchangeTensorPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X ≅
      tensorRight ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y)) :=
  residueExchangeTensorIso ℓ E X ≪≫
    (curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
      (residueExchangeCoefficientPullIso ℓ E f).symm

end AlgebraicGeometry.ProEtale.CondensedRing
