/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.DiagonalCoefficientDiagrams
public import Sheaf.Paper.DiagonalCoefficientPullback

/-! # Pullback of the complete diagonal coefficient family

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-family-pullback).

## Main definitions

- `QuotientPullMap`: the specified balanced-tensor formula.
- `FamilyPullback`: base change at every coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The quotient pullback map is fixed on every balanced tensor generator by
the coefficient pullback and the projection-normalized integral root map.
This definition also applies to ramified quotient levels outside the ell-power
cofinal subsystem. Source: blueprint clause 3 and proof step 3c
(blueprint: def-sfb-diagonal-coefficient-family-pullback). -/
def QuotientPullMap (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (m : (upperStar Ab.{u + 1} f).obj (quotientLine l E π n S).X ⟶
      (quotientLine l E π n X).X) : Prop :=
  (upperStar Ab.{u + 1} f).map
      (Mod.extendπ (coefficientMap (quotientMap l E π n) S) (spIntegralTwist S l E)) ≫ m =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f)
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) S)
      (spIntegralTwist S l E).X ≫
    (condensedPullbackHom
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f ⊗ₘ
      spIntegralComparison f l E) ≫
    Mod.extendπ (coefficientMap (quotientMap l E π n) X) (spIntegralTwist X l E)

/-- Base change of the whole coefficient family, using the published root,
localization and finite-field-colimit comparisons. The additional quotient
clause fixes its tensor comparison on all generators. Source: blueprint clause 3
(blueprint: def-sfb-diagonal-coefficient-family-pullback). -/
structure FamilyPullback (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y'] (family : Family l Y) (family' : Family l Y') where
  [invertibleP : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
  [invertibleP' : ∀ x : ProjectiveLine Y', Invertible (l : (ProjectiveLine Y').residueField x)]
  [invertibleW : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
  [invertibleW' : ∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x)]
  rootsP : CartesianAdicComparison l (baseP g)
  rootsW : CartesianAdicComparison l (baseW g)
  zl : PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
    (zlLine l) family.zl family'.zl
    (spIntegralComparison (baseP g) l (bottomField l))
    (spIntegralComparison (baseW g) l (bottomField l))
  integral : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    PullbackCompatibility (Profinite.continuousMapRingObj.{u} E.1) g
      (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E)
      (rootsP.rational E) (rootsW.rational E)
  closure : PullbackCompatibility (Profinite.padicAlgClRingObj.{u} l) g
    (fun X ↦ spQbarTwist X l) family.closure family'.closure rootsP.qbar rootsW.qbar
  quotients : ∀ (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (d' : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y' (quotientLine l E π n)),
    ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family.integral E) d →
    ScalarCompatibility (quotientMap l E π n) Y'
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family'.integral E) d' →
    ∃ (mP : (upperStar Ab.{u + 1} (baseP g)).obj
        (quotientLine l E π n (ProjectiveLine Y)).X ⟶
          (quotientLine l E π n (ProjectiveLine Y')).X)
      (mW : (upperStar Ab.{u + 1} (baseW g)).obj
        (quotientLine l E π n (diagonalSurface Y)).X ⟶
          (quotientLine l E π n (diagonalSurface Y')).X),
      QuotientPullMap l E π n (baseP g) mP ∧ QuotientPullMap l E π n (baseW g) mW ∧
        Nonempty (PullbackCompatibility
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
          (quotientLine l E π n) d d' mP mW)


end AlgebraicGeometry.ProEtale.DiagonalCoefficients
