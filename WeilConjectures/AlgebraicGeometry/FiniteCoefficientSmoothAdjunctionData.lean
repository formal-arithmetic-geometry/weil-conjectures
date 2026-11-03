/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.GeneralFieldChartAdjunctionRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Finite smooth chart adjunction data for the arbitrary finite-coefficient route.

This is the existence sub-step of `lem-pur-finite-coefficient-adjoint-comparisons`.
The data records only finite-ctf domains, the two chart adjunctions and their
counit-preserving realizations; the coefficient mate and chart equations are a
separate sub-step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale
open GeneralFieldChart

structure FiniteCoefficientSmoothAdjunctionData
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) where
  hFA : ∀ M : chartCtfCategory X A,
    chartCtf Y A ((chartCompact A j p).obj M.obj)
  hFB : ∀ M : chartCtfCategory X B,
    chartCtf Y B ((chartCompact B j p).obj M.obj)
  hSX : ∀ M : chartCtfCategory X A,
    chartCtf X B ((chartScalar φ X).obj M.obj)
  hSY : ∀ K : chartCtfCategory Y A,
    chartCtf Y B ((chartScalar φ Y).obj K.obj)
  GA : chartCtfCategory Y A ⥤ chartCtfCategory X A
  GB : chartCtfCategory Y B ⥤ chartCtfCategory X B
  adjA : chartCtfCompact A j p hFA ⊣ GA
  adjB : chartCtfCompact B j p hFB ⊣ GB
  RA : ChartAdjunctionRealization A j p hFA GA adjA
  RB : ChartAdjunctionRealization B j p hFB GB adjB
  hbAll : ∀ M : chartCtfCategory X A,
    IsIso ((chartCompactScalarComparison φ j p).app M.obj)
  hb : ∀ K : chartCtfCategory Y A,
    IsIso ((chartCompactScalarComparison φ j p).app (GA.obj K).obj)

private theorem finiteCoefficientSmooth_domains
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    (∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj)) ∧
    (∀ M : chartCtfCategory X B,
      chartCtf Y B ((chartCompact B j p).obj M.obj)) ∧
    (∀ M : chartCtfCategory X A,
      chartCtf X B ((chartScalar φ X).obj M.obj)) ∧
    (∀ K : chartCtfCategory Y A,
      chartCtf Y B ((chartScalar φ Y).obj K.obj)) := by
  obtain ⟨nA, hnA⟩ := hA
  obtain ⟨nB, hnB⟩ := hB
  have hA0 : ((ℓ ^ nA : ℕ) : A) = 0 := by
    simpa only [nsmul_eq_mul, mul_one] using hnA (1 : A)
  have hB0 : ((ℓ ^ nB : ℕ) : B) = 0 := by
    simpa only [nsmul_eq_mul, mul_one] using hnB (1 : B)
  let N := nA + nB + 1
  have hN : 0 < N := Nat.zero_lt_succ _
  have hA0' : (ℓ : A) ^ nA = 0 := by simpa only [Nat.cast_pow] using hA0
  have hB0' : (ℓ : B) ^ nB = 0 := by simpa only [Nat.cast_pow] using hB0
  have hA0N : ((ℓ ^ N : ℕ) : A) = 0 := by
    simp [N, Nat.cast_pow, pow_add, hA0']
  have hB0N : ((ℓ ^ N : ℕ) : B) = 0 := by
    simp [N, Nat.cast_pow, pow_add, hB0']
  have hD := generalFieldChartDomains ℓ pchar hp hℓ k j p φ N hN hA0N hB0N
  have hFA := (hD.1 A hA0N).2.1
  have hFB := (hD.1 B hB0N).2.1
  exact ⟨hFA, hFB, hD.2.1, hD.2.2.1⟩

/-- Existence of the finite chart adjunction data.

Source: the Existence and chart-realization paragraphs of
`sk-lem-sp-reduction-exceptional.proof.md`.
This is strictly the data-construction sub-step: no coefficient comparison
morphism, invertibility assertion about that mate, or chart equation is included.
(blueprint: lem-pur-finite-coefficient-adjoint-data-smooth).
Proof: choose a common positive ell-power annihilator. The finite-ctf domain
theorem restricts compact support and both scalar functors. On each smooth etale
coordinate chart, the summation adjunction and ordered projective-line integration
construct the inverse-image/Tate/shift right adjoint. Uniqueness of right adjoints
identifies this chart construction with the ordinary exceptional right adjoint.
The coordinate cover detects constructibility and finite Tor amplitude, so that
adjoint restricts to finite-ctf inputs. This uses the coordinate adjunctions before
global smooth purity. Transport the restricted adjunction through
the finite-ctf site equivalence. Its canonical counit equation supplies RA and RB.
The compact-support scalar/site square is invertible on every finite-ctf object,
so in particular on the image of GA; record both forms of this fact.
-/
theorem finiteCoefficientSmoothAdjunctionData_exists
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))]
    (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    Nonempty (FiniteCoefficientSmoothAdjunctionData ℓ pchar hp hℓ k j p φ hA hB) := by sorry

end AlgebraicGeometry.ProEtale
