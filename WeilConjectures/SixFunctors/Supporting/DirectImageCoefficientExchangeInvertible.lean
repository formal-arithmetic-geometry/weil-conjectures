/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
import WeilConjectures.SmoothPurity.PurCompactSupport.FiniteFreeProperScalarComparison
import WeilConjectures.SixFunctors.Supporting.DirectImageScalarRealizationSquare
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

/-! # Invertibility of the realized direct-image coefficient mate

Source: lem-fix-operation-reduction, direct-image and final paragraphs
(blueprint: lem-weil-direct-image-coefficient-exchange-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem completeUnrestricted
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource.{u, u} l E W)) (hM : IsSfDerivedComplete l E W M) :
    IsDerivedCompleteUnrestricted l E W M := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E W D hl M).mp hM⟩

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
private theorem reconstruction_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : StrictDirectImageMixedUnit.LimitComparison l E f)
    (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((directImageReconstruction l E f C).app K.obj) := by
  have : IsIso (((FrobeniusExchange.models l E).system X).adjunction.unit.app K.obj) :=
    (FrobeniusExchange.models l E).complete X K
  change IsIso ((completedDirectImageComparison l E f).inv.app K.obj ≫
    (sfCompletedDerivedDirectImage l E f).map
      (((FrobeniusExchange.models l E).system X).adjunction.unit.app K.obj) ≫
    C.derived.inv.app ((FrobeniusExchange.reduction l E X).obj K.obj))
  infer_instance

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  [fo : f.IsOver (Spec (.of K₀))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include hl xo yo xft xqc yft yqc fo fs fft fqc

-- The assigned signature retains geometric hypotheses unused by this proof route.
set_option linter.unusedSectionVars false in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- The realized direct-image coefficient mate is invertible on each integral
constructible input. This assertion concerns the actual whole-system mate, before
any Frobenius square or scalar localization.
Source: blueprint lem-fix-operation-reduction, direct-image and final paragraphs;
Deligne, Weil II, (1.1.10)--(1.1.14)
(blueprint: lem-weil-direct-image-coefficient-exchange-invertible).
Proof: the finite extension of complete discrete valuation rings O_E -> O_L is
finite free. In a basis, ordinary completed-coefficient scalar extension is a
finite direct sum and commutes with section direct image. The tensor comparison
is O_L-linear and basis independent, since its two composites are the identity
on tensor generators. Deriving gives the ordinary coefficient comparison, fixed
by its unit/counit mate equation. The finite-free functor commutes with products
and cones and therefore with the Roos model of total derived inverse limit.
Use the normalized reduction counits to compare this ordinary coefficient map
with coefficientExchange: expand scalarSourceComparison and scalarReductionIso,
move the reduction counit past direct image by its naturality, and use the scalar
pullback mate equation defining systemDirectScalar. Both resulting adjuncts are
the ordinary counit tensored with identity. Injectivity of the adjunction Hom
equivalence identifies the realized map with the ordinary invertible comparison,
conjugated by the normalized Roos realization isomorphisms. This proves the
assertion without asserting invertibility of systemDirectScalar on arbitrary
systems, or flatness of any finite quotient-ring coefficient map. -/
theorem directImageCoefficientExchange_isIso
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((FrobeniusExchange.coefficientExchange l E L ι
      (FrobeniusExchange.systemDirect l E f) (FrobeniusExchange.systemDirect l L f)
      (FrobeniusExchange.systemDirectScalar l E L ι f)).app K) := by
  obtain ⟨CE⟩ := directImageLimitComparison l E f
  obtain ⟨CL⟩ := directImageLimitComparison l L f
  let Q := (sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K
  have hE := reconstruction_isIso l E f CE K
  have hL := reconstruction_isIso l L f CL Q
  have hK := completeUnrestricted l E X K.obj K.property.1
  have hD := FrobeniusExchange.directImage_constructible l E K₀ hl f K
  have hχX : IsIso ((completedScalarComparison l E L ι X).app K.obj) :=
    ((finiteFreeCompletedScalarComparison l E L ι X).2.1 K.obj hK).1
  have hχY : IsIso ((completedScalarComparison l E L ι Y).app
      ((FrobeniusExchange.integralDirectImage l E f).obj K.obj)) :=
    ((finiteFreeCompletedScalarComparison l E L ι Y).2.1 _
      (completeUnrestricted l E Y _ hD.1)).1
  have hOrd : IsIso
      ((PurCompactSupport.properComparison (PurCompactSupport.completedChange l E L ι) f).app
        K.obj) :=
    PurCompactSupport.properComparison_isIso_of_finiteFree
      (PurCompactSupport.completedChange l E L ι) f
      (completedScalarRelativeDegree l E L ι)
      (finiteFreeCompletedScalarComparison l E L ι Y).1 K.obj
  have hs := directImageScalarRealizationSquare l E L ι f CE CL K
  have hc : IsIso
      ((completedDerivedScalarExtension l E L ι Y).map
          ((directImageReconstruction l E f CE).app K.obj) ≫
        (completedScalarComparison l E L ι Y).app
          ((FrobeniusExchange.integralDirectImage l E f).obj K.obj) ≫
        (FrobeniusExchange.coefficientExchange l E L ι
          (FrobeniusExchange.systemDirect l E f) (FrobeniusExchange.systemDirect l L f)
          (FrobeniusExchange.systemDirectScalar l E L ι f)).app K) := by
    rw [hs]
    change IsIso
      ((PurCompactSupport.properComparison (PurCompactSupport.completedChange l E L ι) f).app
          K.obj ≫
        (PurCompactSupport.push (PurCompactSupport.completed l L) f).map
          ((completedScalarComparison l E L ι X).app K.obj) ≫
        (directImageReconstruction l L f CL).app Q.obj)
    infer_instance
  have : IsIso
      ((completedScalarComparison l E L ι Y).app
          ((FrobeniusExchange.integralDirectImage l E f).obj K.obj) ≫
        (FrobeniusExchange.coefficientExchange l E L ι
          (FrobeniusExchange.systemDirect l E f) (FrobeniusExchange.systemDirect l L f)
          (FrobeniusExchange.systemDirectScalar l E L ι f)).app K) :=
    IsIso.of_isIso_comp_left
      ((completedDerivedScalarExtension l E L ι Y).map
        ((directImageReconstruction l E f CE).app K.obj)) _
  exact IsIso.of_isIso_comp_left
    ((completedScalarComparison l E L ι Y).app
      ((FrobeniusExchange.integralDirectImage l E f).obj K.obj)) _

end WeilConjectures
