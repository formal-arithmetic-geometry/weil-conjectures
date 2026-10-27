/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.DirectImagesConstructible
import Sheaf.Paper.ProperIntegralTowerComparison
import all Sheaf.Paper.SfIntegralPullbackLinearAdjunction
import all Sheaf.Paper.SfRationalDirectImageAdjunction

/-! # The finite rational adjunction for proper compact support

Source: SGA 4 XVII, §5; Bhatt--Scholze 6.7.2.
(blueprint: lem-zl-proper-support-finite-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FrobeniusExchange

private def properIntegralAdjunction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of D.k))] [IsProper p]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E p ⊣
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper p) E := by
  let DX := (models l E).system X
  let DY := (models l E).system Y
  let iX := (sfIntegralConstructible l E X).ι
  let iY := (sfIntegralConstructible l E Y).ι
  let t := whiskerLeft iY (integralComparisonPullbackCounit l E p DY DX
    ((models l E).roos X) ((models l E).pullback p))
  let : ∀ K : sfIntegralConstructibleCategory l E Y, IsIso (t.app K) :=
    fun K ↦ (models l E).effective p K
  let := NatIso.isIso_of_isIso_app t
  let e : iY ⋙ (DY.reduction ⋙ integralComparisonDerivedSequencePullback l E p) ≅
      constructibleIntegralPullback l E p ⋙ (iX ⋙ DX.reduction) := (asIso t).symm
  let a := DY.adjunction.comp (systemAdjunction l E p)
  let adj : constructibleIntegralPullback l E p ⊣
      directImageFunctor l E D.k (finiteFieldDatumPrimeUnit D l hl) p :=
    a.restrictFullyFaithful (sfIntegralConstructible l E Y).fullyFaithfulι
      (CategoryTheory.faithfulIntegralReduction iX
        (sfIntegralConstructible l E X).fullyFaithfulι
        DX.adjunction ((models l E).complete X)) e (Iso.refl _)
  let c : sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper p) E ≅
      directImageFunctor l E D.k (finiteFieldDatumPrimeUnit D l hl) p :=
    ((sfIntegralConstructible l E Y).fullyFaithfulι.whiskeringRight _).preimageIso
      (ProperIntegralTower.integralComparison l E D hl p)
  exact adj.ofNatIsoRight c.symm

/-- Proper compact support is right adjoint to the actual finite rational pullback.
Source: SGA 4 XVII, §5; Bhatt--Scholze 6.7.2
(blueprint: lem-zl-proper-support-finite-adjunction).
Proof: remove the identity open on the strict compact-support tower and pass the
resulting tower isomorphism through total limit. Full constructible inclusion
reflects this isomorphism. Restrict the reduction/limit and system adjunctions
using the normalized pullback realization. Transport the right adjoint along the
identity-open comparison. Tensor its unit and counit with one; tensor induction
proves naturality and the two triangles. The pure-tensor characterization of
rational pullback identifies the localized left functor with the recorded one,
and the localized right functor is the literal finite support functor. -/
theorem properSupportFiniteAdjunction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of D.k))] [IsProper p]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    Nonempty (rationalDerivedPullback l E p ⊣
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper p) E) := by
  let I := constructibleIntegralPullback l E p
  let R := sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
    (Compactification.ofIsProper p) E
  let a := properIntegralAdjunction D l hl E p
  have : R.Additive := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (finiteFieldDatumPrimeUnit D l hl) (Compactification.ofIsProper p) E).1
  have : R.Linear (Padic.coefficientExtensionIntegers l E) :=
    (sfCompactSupportFiniteIntegralFunctor_linear l D.k
      (finiteFieldDatumPrimeUnit D l hl) (Compactification.ofIsProper p) E).2
  have : I.Additive := CategoryTheory.additiveLeftOfLinearRight a
  have : I.Linear (Padic.coefficientExtensionIntegers l E) :=
    CategoryTheory.linearLeftOfLinearRight _ a
  let π := Padic.coefficientExtensionUniformizer l E
  let O := Padic.coefficientExtensionIntegers l E
  let Lq := ScalarLocalization.liftLinear O π I
  have hL : Lq = rationalDerivedPullback l E p := by
    apply (rationalDerivedPullback_existsUnique l E p).unique _
      (rationalDerivedPullback_existsUnique l E p).exists.choose_spec
    refine ⟨inferInstance, (fun _ ↦ rfl), ?_⟩
    intro K N b c
    exact heq_of_eq (ScalarLocalization.liftLinear_tmul O π I c b)
  have aq := ScalarLocalization.liftAdjunction O π I R a
  change Lq ⊣ sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
    (Compactification.ofIsProper p) E at aq
  rw [hL] at aq
  exact ⟨aq⟩

end WeilConjectures
