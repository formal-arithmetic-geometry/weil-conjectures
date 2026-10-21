/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.RealizationCompletedPullData

/-! # Ordinary scalar pullback comparisons

Source: BS Proposition 6.6.11, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-pull-ordinary-system). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {k : Type u} [Field k]

/-- Ordinary scalar comparison and its identity and composition equations.
Source: BS Lemma 6.8.2 and Remark 6.8.15. Completion is retained in the arrow
only through its specified unit; the laws below concern ordinary pullback.
(blueprint: lem-weil-pbc-realization-pull-ordinary-system) -/
structure RealizationPullOrdinarySystem
    (scalar : ∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme) where
  arrow : ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
    RealizationCompletedPullArrow T U h.left (scalar T) (scalar U)
  coefficient_comp : realizationPullLawCoefficientComp scalar arrow
  rationalComp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
    (arrow j).continuousPull ⋙ (arrow h).continuousPull ≅ (arrow (h ≫ j)).continuousPull
  rationalComp_canonical : realizationPullLawRationalCompCanonical scalar arrow rationalComp
  ordinary_comp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V)
    (K : PbcCompletedDerived V.scheme (pbcIntegralDatum l E)),
    (pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).map
        ((pbcActualDerivedPullCompIso h.left j.left (pbcIntegralDatum l E)).inv.app K) ≫
      (arrow (h ≫ j)).ordinaryComparison.hom.app K =
    (arrow h).ordinaryComparison.hom.app
        ((pbcActualDerivedPull j.left (pbcIntegralDatum l E)).obj K) ≫
      (arrow h).continuousPull.map ((arrow j).ordinaryComparison.hom.app K) ≫
      (rationalComp h j).hom.app
        ((pbcDerivedExtend (realizationPullScalarMap l E (scalar V))).obj K)
  moduleId : ∀ T : RealizationPullScheme l k,
    proEtaleRingModulePullback (𝟙 T.scheme) (rationalCoefficientSheaf l T.scheme E)
      (rationalCoefficientSheaf l T.scheme E) (arrow (𝟙 (Over.mk
        (T.scheme ↘ Spec (.of k))))).rationalCoefficient ≅ 𝟭 _
  moduleId_unit : realizationPullLawModuleIdUnit scalar arrow moduleId
  continuousId : ∀ T : RealizationPullScheme l k,
    (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).continuousPull ≅ 𝟭 _
  continuousId_normalization :
    realizationPullLawContinuousIdNormalization scalar arrow moduleId continuousId
  ordinary_id : ∀ (T : RealizationPullScheme l k)
    (K : PbcCompletedDerived T.scheme (pbcIntegralDatum l E)),
    (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).ordinaryComparison.hom.app K ≫
      (continuousId T).hom.app
        ((pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).obj K) =
    (pbcDerivedExtend (realizationPullScalarMap l E (scalar T))).map
      ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T.scheme).hom.app K)

/-- Existence of the ordinary normalized comparison system.
Source: BS Proposition 6.6.11, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-pull-ordinary-system)

Proof: the finite-projection equations identify the completed coefficient map with
the canonical profinite comparison. In continuous integral coordinates reduction
commutes with precomposition, so the same map precomposes functions. Localization
at the uniformizer yields the rational coefficient iso and its scalar square.
Pull back each finite locally closed stratum and its pro-etale trivializing cover;
weakly etale and fpqc base change preserve the cover. Ordinary pullback of the
constant perfect complex is the same bounded finite-projective complex with its
coefficients pulled back. The stratified perfect characterization therefore puts
ordinary pullback in the integral category. The normalized reduction-tower comparison
carries the strict augmentation to this object's quotient augmentation. Naturality
of the constant-tower adjunction unit and intrinsic-to-tower completeness make the
specified strict unit invertible and put completed pullback in the same full category.
The actual coefficient maps preserve constant A-scalars. Thus ordinary pullback is
A-linear; conjugating by the invertible unit gives the completed linear restriction.
The unit-normalized localization inverse-image comparison gives the module comparison,
its fraction formula and its termwise chain iso. Its exact derived comparison has the
stated counit normalization. Compose with scalar extension of the inverse completion
unit to obtain alpha and its normalization. The localization comparison's identity
and composition equations give ordinary_comp and ordinary_id. The rational coefficient
compositor and identity are the actual ringed pullback comparisons, whose module-unit
and cochain-representative equations give the remaining fields. -/
theorem realizationPullOrdinarySystem
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (scalar : ∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme) :
    Nonempty (RealizationPullOrdinarySystem scalar) := by
  sorry

end WeilConjectures
