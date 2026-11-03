/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalComparisonIsomorphisms
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCoefficientCoherence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor

/-! # Domains of the finite exceptional tensor comparison

Source: latest blueprint, reduction compatibilities proof (3), Tensor map, domains.
(blueprint: lem-pur-finite-exceptional-tensor-domains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

namespace AlgebraicGeometry.ProEtale.FiniteExceptionalTensor

private theorem ordinary_unit (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    ctf A T (𝟙_ (D A T)) := by
  exact (CondensedRing.ordinary_ctf_iff A T _).2
    (coherenceCtf_unit (ULift.{u + 1} A) T)

private theorem ordinary_pull (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) {K : D A Y} (hK : ctf A Y K) :
    ctf A X ((pull A f).obj K) := by
  exact (CondensedRing.ordinary_ctf_iff A X _).2
    (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj f
      ((CondensedRing.ordinary_ctf_iff A Y K).1 hK))

private theorem ordinary_tensor (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    {K M : D A T} (hK : ctf A T K) (hM : ctf A T M) : ctf A T (K ⊗ M) := by
  exact (CondensedRing.ordinary_ctf_iff A T _).2
    (coherenceCtf_tensor (ULift.{u + 1} A) T
      ((CondensedRing.ordinary_ctf_iff A T K).1 hK)
      ((CondensedRing.ordinary_ctf_iff A T M).1 hM))

private theorem ordinary_scalar
    (ell : ℕ) [Fact ell.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    {K : D A T} (hK : ctf A T K) : ctf B T ((scalar φ T).obj K) := by
  have hg := (reductionGood_realization_iff T A K).2
    ((CondensedRing.ordinary_ctf_iff A T K).1 hK)
  have hs := reductionGood_scalar ell hA hB φ T _ hg
  apply (CondensedRing.ordinary_ctf_iff B T _).2
  apply (reductionGood_realization_iff T B _).1
  exact reductionGood_iso
    ((sfIntrinsicDerivedEquivalence T B).counitIso.app _).symm hs

/-- All domains and ordinary comparison isomorphisms used in the tensor calculation.
No assertion about the exceptional scalar mate or the desired tensor equality is made.
Source: latest blueprint, reduction compatibilities proof (3), Tensor map; the finite
coefficient equivalence, constructible stability, compact-support projection and
finite-coefficient compact-support comparison.
(blueprint: lem-pur-finite-exceptional-tensor-domains).

Proof: Equip A and B with their discrete topology. The normalized finite-coefficient
encoding identifies ordinary bounded constructible finite-Tor complexes with the
intrinsic ones, preserves the constant tensor unit and the derived tensor, and commutes
with pullback and compact support. The unit is bounded, constructible and flat. The
restricted right adjoints take values in Dctf by their codomains. Pullback, tensor and
scalar extension preserve Dctf, so they give all ten asserted membership conditions,
including the scalar extension of the A tensor domain. Apply the finite-ring projection
theorem to K and omega in both coefficient categories. Apply the finite-coefficient
compact-support scalar comparison to G_A K, omega_A and their tensor domain. Its
proper factor agrees with compactComparison by the proper Hom bijection; the open
factor agrees by its extension-by-zero unit normalization. Finally scalar tensor and
scalar/pullback balancing are invertible: on flat-term K-flat representatives these
are the ordinary balanced scalar tensor and geometric pullback identifications. The
constant unit is K-flat and scalar-unit multiplication identifies its extension with
the B unit. Localization and the scalar adjunction give the specified sigma and
scalarUnit for any presentations aX and aY. The algebraically closed base has finite
ell-cohomological dimension; its characteristic differs from ell by the hypotheses.
All these arguments include zero coefficient rings and empty schemes. -/
theorem exceptional_tensor_domains
    (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) (_hell : ell.Prime) (_hellp : ell ≠ D₀.p)
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ ∀ r : A, (ell ^ n) • r = 0)
    (_hB : ∃ n : ℕ, 1 ≤ n ∧ ∀ r : B, (ell ^ n) • r = 0)
    (φ : A →+* B) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))]
    [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (Y ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))]
    [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) [c.Z.Over (Spec (.of D₀.k))]
    [IsSeparated (c.Z ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D₀.k))]
    [QuasiCompact (c.Z ↘ Spec (.of D₀.k))]
    [c.i.IsOver (Spec (.of D₀.k))] [c.g.IsOver (Spec (.of D₀.k))]
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (hPA : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (hPB : ∀ M : C B X, ctf B Y ((support B c).obj M.obj))
    (GA : C A Y ⥤ C A X) (GB : C B Y ⥤ C B X)
    (_adjA : smallSupport A c hPA ⊣ GA) (_adjB : smallSupport B c hPB ⊣ GB)
    (K : C A Y) :
    ∃ (hIA : ctf A Y (𝟙_ (D A Y))) (hIB : ctf B Y (𝟙_ (D B Y)))
      (_hSK : ctf B Y ((scalar φ Y).obj K.obj))
      (_hSC : ctf B X ((scalar φ X).obj (GA.obj K).obj))
      (_hSI : ctf B Y ((scalar φ Y).obj (𝟙_ (D A Y))))
      (_hSω : ctf B X ((scalar φ X).obj (omega A GA hIA)))
      (_hDA : ctf A X ((pull A f).obj K.obj ⊗ omega A GA hIA))
      (_hDB : ctf B X ((pull B f).obj ((scalar φ Y).obj K.obj) ⊗ omega B GB hIB))
      (_hπA : IsIso (projection A c K.obj (omega A GA hIA)))
      (_hπB : IsIso (projection B c ((scalar φ Y).obj K.obj) (omega B GB hIB)))
      (_hbK : IsIso (compactComparison φ c aX aY (GA.obj K).obj))
      (_hbI : IsIso (compactComparison φ c aX aY (omega A GA hIA)))
      (_hσ : IsIso (sigma φ f aX aY K.obj (omega A GA hIA)))
      (_hu : IsIso (scalarUnit φ Y aY)),
      ctf B X ((scalar φ X).obj ((pull A f).obj K.obj ⊗ omega A GA hIA)) ∧
        IsIso (compactComparison φ c aX aY ((pull A f).obj K.obj ⊗ omega A GA hIA)) := by
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D₀.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D₀.k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D₀.k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D₀.k))
  have : Fact ell.Prime := ⟨_hell⟩
  have ha : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0 := by
    obtain ⟨n, _, hn⟩ := _hA
    exact ⟨n, hn⟩
  have hb : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0 := by
    obtain ⟨n, _, hn⟩ := _hB
    exact ⟨n, hn⟩
  have hIA := ordinary_unit A Y
  have hIB := ordinary_unit B Y
  have hSK := ordinary_scalar ell ha hb φ Y K.property
  have hSC := ordinary_scalar ell ha hb φ X (GA.obj K).property
  have hSI := ordinary_scalar ell ha hb φ Y hIA
  have hSω := ordinary_scalar ell ha hb φ X (GA.obj ⟨𝟙_ (D A Y), hIA⟩).property
  have hDA := ordinary_tensor A X (ordinary_pull A f K.property)
    (GA.obj ⟨𝟙_ (D A Y), hIA⟩).property
  have hDB := ordinary_tensor B X (ordinary_pull B f hSK)
    (GB.obj ⟨𝟙_ (D B Y), hIB⟩).property
  have hSD := ordinary_scalar ell ha hb φ X hDA
  obtain ⟨hπA, hπB, hcomp, hsigma, hunit⟩ :=
    finite_exceptional_comparison_isomorphisms D₀ ell _hell _hellp A B _hA _hB
      φ f c aX aY
  exact ⟨hIA, hIB, hSK, hSC, hSI, hSω, hDA, hDB,
    hπA K.obj _ K.property (GA.obj ⟨𝟙_ (D A Y), hIA⟩).property,
    hπB _ _ hSK (GB.obj ⟨𝟙_ (D B Y), hIB⟩).property,
    hcomp _ (GA.obj K).property,
    hcomp _ (GA.obj ⟨𝟙_ (D A Y), hIA⟩).property,
    hsigma _ _, hunit, hSD, hcomp _ hDA⟩

end AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
