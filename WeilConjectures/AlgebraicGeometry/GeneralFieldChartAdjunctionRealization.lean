/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteP1CoefficientSplitting
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.SmoothPurity.CounitTensorTower
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
public import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarNormalForm
public import WeilConjectures.AlgebraicGeometry.GeneralFieldBrownRightAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition
public import WeilConjectures.AlgebraicGeometry.GeneralFieldChart.FiniteCoefficientChartAdjunctionData

/-!
# General-field finite-chart adjunction realization

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`,
Locality and Charts (blueprint: `lem-pur-general-field-chart-adjunction-realization`).

The statement records the finite-ctf comparison, the canonical compact-support
realization and counit, and the normalized ordered chart comparison.  Its proof is
deferred: (1) restrict the site comparison to finite-Tor constructible complexes
and reflect Tor intervals; (2) use the proper/open comparison `s_R`; (3) transport
the ordinary etale adjunction and its counit and identify the restricted right
adjoint by the displayed unique counit-preserving comparison; (4) paste the
etale-summation and ordered affine adjunctions; and (5) apply the scalar normal-form
equation, including its zero-dimensional unit.-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- General-field finite-chart realization with its canonical comparison and chart
normalization.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: `lem-pur-general-field-chart-adjunction-realization`).
The five proof steps are: finite-site equivalence and Tor reflection;
proper/open comparison and compact-support preservation; transport of the ordinary
adjunction with counit `C_W(v) ∘ s_R⁻¹` and the unique counit-preserving restricted
right-adjoint comparison; ordered etale plus affine chart composition, with the
canonical intrinsic chart iso and its actual realization counit; and the
scalar/tensor/Tate/shift normal form, whose zero-dimensional component is the unit
comparison. -/
theorem generalFieldChartAdjunctionRealization
    (p ell : ℕ) [Fact ell.Prime] (hp : 0 < p) (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (r : Z ⟶ Y) [IsProper r] [r.IsOver (Spec (.of k))]
    (hr : j ≫ r = h)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (n : ℕ) (hn : 1 ≤ n) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor Y A
          ((reductionCompactSupport A j r).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
        spFiniteConstructibleTor Y B
          ((reductionCompactSupport B j r).obj M.obj))
      (hXA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor X B
          ((scalarExtensionFunctor φ X).obj M.obj))
      (hYA : ∀ M : spFiniteConstructibleTorCategory Y A,
        spFiniteConstructibleTor Y B
          ((scalarExtensionFunctor φ Y).obj M.obj))
      (hν : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))]
        (R : Type u) [CommRing R] [Finite R],
        (comparisonUpperStarPlusEtaleOrigin
          (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).IsEquivalence)
      (hνctf : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))]
        (R : Type u) [CommRing R] [Finite R],
        ∃ (C :
          (Etale.DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).FullSubcategory ⥤
            spFiniteConstructibleTorCategory T R),
          C.IsEquivalence ∧
            ∀ K, (C.obj K).obj = (reductionSite R T).obj K.obj)
      (hTor : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))]
        (R : Type u) [CommRing R] [Finite R]
        (a b : ℤ)
        (K : _root_.DerivedCategory
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))),
        (AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn
           (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T a b
           (D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1, u} R)]).obj K) ↔
         Etale.DerivedCategory.torAmplitudeIn
           (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T a b K))
      (hPullA : ∀ (T U : Scheme.{u}) [T.Over (Spec (.of k))]
        [U.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))]
        [QuasiCompact (U ↘ Spec (.of k))]
        [IsSeparated (U ↘ Spec (.of k))] (i : U ⟶ T)
        (K : spFiniteConstructibleTorCategory T A),
        spFiniteConstructibleTor U A
          ((proEtaleConstantRingDerivedPullback A i).obj K.obj))
      (hPullB : ∀ (T U : Scheme.{u}) [T.Over (Spec (.of k))]
        [U.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))]
        [QuasiCompact (U ↘ Spec (.of k))]
        [IsSeparated (U ↘ Spec (.of k))] (i : U ⟶ T)
        (K : spFiniteConstructibleTorCategory T B),
        spFiniteConstructibleTor U B
          ((proEtaleConstantRingDerivedPullback B i).obj K.obj))
      (hShiftA : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))] (z : ℤ)
        (K : spFiniteConstructibleTorCategory T A),
        spFiniteConstructibleTor T A
          ((shiftFunctor (proEtaleDerivedCategory T A) z).obj K.obj))
      (hShiftB : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))] (z : ℤ)
        (K : spFiniteConstructibleTorCategory T B),
        spFiniteConstructibleTor T B
          ((shiftFunctor (proEtaleDerivedCategory T B) z).obj K.obj))
      (hTateA : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))] [IsNoetherian T]
        (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))) (d : ℕ)
        (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T),
        let TA := Scheme.finiteEtaleTateTwist T (ell ^ n)
          (ULift.{u + 1, u} A)
          (congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA) d
        Etale.DerivedCategory.boundedConstructibleFiniteTor
          (ULift.{u + 1, u} A) T K →
          Etale.DerivedCategory.boundedConstructibleFiniteTor
            (ULift.{u + 1, u} A) T
            (((Etale.derivedTensor
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj TA)))
      (hTateB : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))]
        [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))] [IsNoetherian T]
        (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))) (d : ℕ)
        (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T),
        let TB := Scheme.finiteEtaleTateTwist T (ell ^ n)
          (ULift.{u + 1, u} B)
          (congrArg (fun a : B => (⟨a⟩ : ULift.{u + 1, u} B)) hB) d
        Etale.DerivedCategory.boundedConstructibleFiniteTor
          (ULift.{u + 1, u} B) T K →
          Etale.DerivedCategory.boundedConstructibleFiniteTor
            (ULift.{u + 1, u} B) T
            (((Etale.derivedTensor
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj TB))),
      ∃ (GA : spFiniteConstructibleTorCategory Y A ⥤
          spFiniteConstructibleTorCategory X A)
        (GB : spFiniteConstructibleTorCategory Y B ⥤
          spFiniteConstructibleTorCategory X B)
        (adjA : reductionCtfCompactSupport A j r hFA ⊣ GA)
        (adjB : reductionCtfCompactSupport B j r hFB ⊣ GB),
        ∃ (RA : ReductionExceptionalRealization A j r hFA GA adjA)
          (RB : ReductionExceptionalRealization B j r hFB GB adjB),
          (letI : IsNoetherian X :=
             isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
           letI : IsNoetherian Y :=
             isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
           let c : Compactification (j ≫ r) :=
             ⟨Z, r, j, rfl, inferInstance, inferInstance⟩
           letI : HasCompactification (j ≫ r) := c.hasCompactification
           ∃ hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)),
           let hΛA : HasInvertibleExponent (ULift.{u + 1, u} A) Y :=
             ⟨ell ^ n, pow_pos (Fact.out : ell.Prime).pos n,
               congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA, hY⟩
           let hΛB : HasInvertibleExponent (ULift.{u + 1, u} B) Y :=
             ⟨ell ^ n, pow_pos (Fact.out : ell.Prime).pos n,
               congrArg (fun b : B => (⟨b⟩ : ULift.{u + 1, u} B)) hB, hY⟩
           let brownA := generalFieldBrownCtfRight k A (Y ↘ Spec (.of k)) (j ≫ r) c hΛA
           let brownB := generalFieldBrownCtfRight k B (Y ↘ Spec (.of k)) (j ≫ r) c hΛB
           ∃ (ρA : reductionCtfCompactSupport A j r hFA ≅
                generalFieldBrownCtfLeft k A (Y ↘ Spec (.of k)) (j ≫ r) c hΛA)
             (ρB : reductionCtfCompactSupport B j r hFB ≅
                generalFieldBrownCtfLeft k B (Y ↘ Spec (.of k)) (j ≫ r) c hΛB),
           generalFieldBrownLeftNormalization k A (Y ↘ Spec (.of k)) j r hFA hΛA ρA ∧
           generalFieldBrownLeftNormalization k B (Y ↘ Spec (.of k)) j r hFB hΛB ρB ∧
           (let adjBrownA := (generalFieldBrownCtfAdjunction
              k A (Y ↘ Spec (.of k)) (j ≫ r) c hΛA).ofNatIsoLeft ρA.symm
            let adjBrownB := (generalFieldBrownCtfAdjunction
              k B (Y ↘ Spec (.of k)) (j ≫ r) c hΛB).ofNatIsoLeft ρB.symm
            (∃! θA : GA ≅ brownA,
              ∀ L, (reductionCtfCompactSupport A j r hFA).map (θA.hom.app L) ≫
                adjBrownA.counit.app L = adjA.counit.app L) ∧
            (∃! θB : GB ≅ brownB,
              ∀ L, (reductionCtfCompactSupport B j r hFB).map (θB.hom.app L) ≫
                adjBrownB.counit.app L = adjB.counit.app L) ∧
            ∀ (θA : GA ≅ brownA) (θB : GB ≅ brownB)
              (_hθA : ∀ L, (reductionCtfCompactSupport A j r hFA).map (θA.hom.app L) ≫
                adjBrownA.counit.app L = adjA.counit.app L)
              (_hθB : ∀ L, (reductionCtfCompactSupport B j r hFB).map (θB.hom.app L) ≫
                adjBrownB.counit.app L = adjB.counit.app L),
           ∀ (d : ℕ) (e : X ⟶ affineTraceTower Y d)
                 [AlgebraicGeometry.Etale e] [IsSeparated e]
                 [LocallyOfFiniteType e] [QuasiCompact e]
                 (he : (𝟙 X) ≫ h = e ≫ affineTraceProjection Y d),
                   let he' : (𝟙 X) ≫ (j ≫ r) = e ≫ affineTraceProjection Y d := by
                     simpa [hr] using he
                   ∃ (o : RA.origin ⋙
                         Etale.scalarExtension
                           (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y ≅
                       reductionCtfScalar φ Y hYA ⋙ RB.origin),
                     (∀ K : spFiniteConstructibleTorCategory Y A,
                       (reductionSite B Y).map (o.hom.app K) ≫
                           RB.originIso.hom.app ((reductionCtfScalar φ Y hYA).obj K) =
                         (reductionSiteScalarIso φ Y).inv.app (RA.origin.obj K) ≫
                           (scalarExtensionFunctor φ Y).map (RA.originIso.hom.app K)) ∧
                     ∃ (tA : Etale.OrdinaryFiniteTwistTransport
                     (ULift.{u + 1, u} A) (ell ^ n)
                     (congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA))
                   (tB : Etale.OrdinaryFiniteTwistTransport
                     (ULift.{u + 1, u} B) (ell ^ n)
                     (congrArg (fun a : B => (⟨a⟩ : ULift.{u + 1, u} B)) hB)),
                   ∃ (DA : ∀ (T : Scheme.{u}) [IsNoetherian T]
                       (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
                       Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A)
                         (ell ^ n)
                         (congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA)
                         tA T hT)
                     (DB : ∀ (T : Scheme.{u}) [IsNoetherian T]
                       (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
                       Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} B)
                         (ell ^ n)
                         (congrArg (fun a : B => (⟨a⟩ : ULift.{u + 1, u} B)) hB)
                         tB T hT),
                     ∃ (MA : Etale.EtaleCompactSupportNormalization
                         (ULift.{u + 1, u} A))
                       (MB : Etale.EtaleCompactSupportNormalization
                         (ULift.{u + 1, u} B)),
                       (∀ K : spFiniteConstructibleTorCategory Y A,
                         ∃ qBrownA :
                           (proEtaleConstantRingDerivedPullback A (𝟙 X)).obj
                               ((brownA.obj K).obj) ≅
                             (reductionSite A X).obj
                               ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) e).obj
                                 ((Etale.affineTraceRight (ULift.{u + 1, u} A) (ell ^ n)
                                   (congrArg (fun a : A =>
                                     (⟨a⟩ : ULift.{u + 1, u} A)) hA) Y d).obj
                                   (RA.origin.obj K))),
                           (proEtaleConstantRingDerivedPullback A (𝟙 X)).map
                               ((θA.hom.app K).hom) ≫ qBrownA.hom =
                             (reductionIntrinsicChartIso A j r hFA GA adjA RA MA
                               (𝟙 X) d e he' (ell ^ n)
                               (congrArg (fun a : A =>
                                 (⟨a⟩ : ULift.{u + 1, u} A)) hA) tA DA hY K).hom) ∧
                       (reductionRealizationCounitEquation A j r hFA GA adjA
                         RA.origin RA.originIso RA.right RA.adjunction
                         RA.right_plus RA.rightIso) ∧
                       (∀ K : spFiniteConstructibleTorCategory Y B,
                         ∃ qBrownB :
                           (proEtaleConstantRingDerivedPullback B (𝟙 X)).obj
                               ((brownB.obj K).obj) ≅
                             (reductionSite B X).obj
                               ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) e).obj
                                 ((Etale.affineTraceRight (ULift.{u + 1, u} B) (ell ^ n)
                                   (congrArg (fun a : B =>
                                     (⟨a⟩ : ULift.{u + 1, u} B)) hB) Y d).obj
                                   (RB.origin.obj K))),
                           (proEtaleConstantRingDerivedPullback B (𝟙 X)).map
                               ((θB.hom.app K).hom) ≫ qBrownB.hom =
                             (reductionIntrinsicChartIso B j r hFB GB adjB RB MB
                               (𝟙 X) d e he' (ell ^ n)
                               (congrArg (fun a : B =>
                                 (⟨a⟩ : ULift.{u + 1, u} B)) hB) tB DB hY K).hom) ∧
                       (reductionRealizationCounitEquation B j r hFB GB adjB
                         RB.origin RB.originIso RB.right RB.adjunction
                         RB.right_plus RB.rightIso) ∧
                       ∃! (c : GA ⋙ reductionCtfScalar φ X hXA ⟶
                           reductionCtfScalar φ Y hYA ⋙ GB),
                         ReductionExceptionalChartEquation ell φ j r d hFA hFB hXA hYA
                           GA GB adjA adjB RA RB c ∧
                         (∀ (K : Etale.DerivedCategoryModule
                               (ULift.{u + 1, u} A) Y)
                            (_hBounded : _root_.DerivedCategory.TStructure.t.bounded K)
                            (_hConstructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
                              ((_root_.DerivedCategory.homologyFunctor
                                (Sheaf Y.smallEtaleTopology
                                  (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) i).obj K))
                            (_hTor : ∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
                              (Sheaf Y.smallEtaleTopology
                                (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) a b K),
                           (reductionEtaleChartScalarIso
                              (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ell ^ n)
                              (congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA)
                              (congrArg (fun b : B => (⟨b⟩ : ULift.{u + 1, u} B)) hB)
                              hY d e K).hom ≫
                             (Etale.finiteAffineChartNormalIso
                               (ULift.{u + 1, u} B) (ell ^ n)
                               (pow_pos (Fact.out : ell.Prime).pos n)
                               (congrArg (fun b : B => (⟨b⟩ : ULift.{u + 1, u} B)) hB)
                               Y hY d e
                               ((Etale.scalarExtension
                                 (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj K)).hom =
                           (Etale.scalarExtension
                             (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).map
                             (Etale.finiteAffineChartNormalIso
                               (ULift.{u + 1, u} A) (ell ^ n)
                               (pow_pos (Fact.out : ell.Prime).pos n)
                               (congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA)
                               Y hY d e K).hom ≫
                           Etale.finiteAffineChartScalarMap
                             (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ell ^ n)
                             (congrArg (fun a : A => (⟨a⟩ : ULift.{u + 1, u} A)) hA)
                             (congrArg (fun b : B => (⟨b⟩ : ULift.{u + 1, u} B)) hB)
                             (e ≫ affineTraceProjection Y d) d (2 * (d : ℤ)) K)
    ))
    := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.GeneralFieldChart

/-- The canonical finite-ctf site equivalence with every Tor interval retained.

Source: general-field chart realization, first paragraph.
(blueprint: lem-pur-general-field-chart-adjunction-realization).
Proof: finite rings are Noetherian. Apply the finite-Tor constructible comparison on
qcqs schemes, using its preserved and reflected Tor intervals. Compose its forward
functor with the section-normalized constant-module realization. The exact comparison
is fully faithful and every constructible finite-Tor complex has an ordinary-etale
origin, giving precisely the displayed restriction equivalence. No perfectness of the
base field, flatness of a coefficient map or smooth coefficient comparison is used.
-/
theorem generalFieldChartSiteEquivalence (k : Type u) [Field k]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (A : Type u) [CommRing A] [Finite A] :
    ∃ hC : ∀ K : (Etale.DerivedCategory.boundedConstructibleFiniteTor
        (ULift.{u + 1, u} A) T).FullSubcategory,
        chartCtf T A ((chartSite A T).obj K.obj),
      ((chartCtf T A).lift
        ((Etale.DerivedCategory.boundedConstructibleFiniteTor
          (ULift.{u + 1, u} A) T).ι ⋙ chartSite A T) hC).IsEquivalence ∧
      ∀ (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T),
        Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} A) T K →
        ∀ a b : ℤ, a ≤ b →
          (Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K ↔
            HasProEtaleTorAmplitude T A ((chartSite A T).obj K) a b) :=
  sorry

/-- Realization of the restricted exceptional adjunction, including its actual counit.

Source: general-field chart realization, transported-adjunction paragraph and Charts.
(blueprint: lem-pur-general-field-chart-adjunction-realization).
Proof: (1) use `generalFieldChartSiteEquivalence` for a functorial finite-ctf origin;
(2) restrict ordinary-etale compact support and its right adjoint to the finite-ctf
categories; (3) transport the adjunction through the equivalence using the canonical
proper/open comparison `chartSiteCompactSupportIso`; its counit is ordinary evaluation
after that comparison and the input-origin isomorphism; (4) use uniqueness of right
adjoints to identify it with the displayed constructible adjunction, retaining the
counit equation in `ChartAdjunctionRealization`. For fixed origin and ordinary right
adjoint, injectivity of the adjunction Hom transposition makes the natural comparison
unique; the equation fixes its hom, hence its inverse; (5) for a coordinate chart, compose
etale summation with the ordered affine trace adjunction and use
`chartEtaleChartRightIso` and `chartNormalIso`. The zero-dimensional case uses units.
The scalar identification is the actual scalar/pullback, balanced Tate and even-shift
comparison `chartScalarReassociationMap`, with no smooth coefficient comparison used.
-/
theorem generalFieldChartAdjunctionRealization
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
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hF : ∀ M : chartCtfCategory X A,
      chartCtf Y A ((chartCompact A j p).obj M.obj))
    (G : chartCtfCategory Y A ⥤ chartCtfCategory X A)
    (adj : chartCtfCompact A j p hF ⊣ G) :
    ∃ R : ChartAdjunctionRealization A j p hF G adj,
      ∃! σ : G ⋙ (chartCtf X A).ι ≅ R.origin ⋙ R.right ⋙ chartSite A X,
        chartRealizationCounitEquation A j p hF G adj R.origin R.originIso
          R.right R.adjunction R.right_plus σ :=
  sorry

/-- Finite-ctf domains for compact support, inverse image/Tate/shift and arbitrary
coefficient extension on both ordinary sites. Canonical comparisons between these
functors therefore restrict, because the subcategories are full.

Source: the first paragraph of general-field chart realization.
(blueprint: lem-pur-general-field-chart-adjunction-realization).
Proof: separated finite-type schemes over a field are Noetherian. Finite coefficients
are Noetherian rings. Constructibility and finite Tor bounds are preserved by ordinary
compact support using the finite-cohomological-dimension and Tor-window statements.
Exact pullback preserves flat constructible models; a finite Tate line is locally free
of rank one and an integral shift translates its bounds. Use the finite-ctf comparison
equivalence and its preserved Tor intervals for the pro-etale assertions. Extension
along the given ring map sends a bounded flat model to a bounded flat B-model on the
same strata; the same Tor test works for every B-module. This proves the scalar clauses
without flatness of B over A. Restrict the actual comparison maps to the full domains.
-/
theorem generalFieldChartDomains
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
    (φ : A →+* B) (n : ℕ) (hn : 0 < n)
    (hA : ((ℓ ^ n : ℕ) : A) = 0) (hB : ((ℓ ^ n : ℕ) : B) = 0) :
    (∀ (R : Type u) [CommRing R] [Finite R] (hR : ((ℓ ^ n : ℕ) : R) = 0),
      (∀ M : (Etale.DerivedCategory.boundedConstructibleFiniteTor
          (ULift.{u + 1, u} R) X).FullSubcategory,
        Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} R) Y
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} R))
            (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).obj
              M.obj)) ∧
      (∀ M : chartCtfCategory X R,
        chartCtf Y R ((chartCompact R j p).obj M.obj)) ∧
      (∀ (a : ℕ) (b : ℤ) (K : (Etale.DerivedCategory.boundedConstructibleFiniteTor
          (ULift.{u + 1, u} R) Y).FullSubcategory),
        Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} R) X
          ((chartEtaleOperation (ULift.{u + 1, u} R) (ℓ ^ n)
            (congrArg ULift.up hR) (j ≫ p) a b).obj K.obj)) ∧
      (∀ (a : ℕ) (b : ℤ) (K : chartCtfCategory Y R),
        chartCtf X R ((sfIntrinsicDerivedEquivalence X R).functor.obj
          ((chartProOperation (ULift.{u + 1, u} R) (ℓ ^ n)
            (congrArg ULift.up hR) (j ≫ p) a b).obj
              ((sfIntrinsicDerivedEquivalence Y R).inverse.obj K.obj))))) ∧
    (∀ K : chartCtfCategory X A,
      chartCtf X B ((chartScalar φ X).obj K.obj)) ∧
    (∀ K : chartCtfCategory Y A,
      chartCtf Y B ((chartScalar φ Y).obj K.obj)) ∧
    (∀ K : (Etale.DerivedCategory.boundedConstructibleFiniteTor
        (ULift.{u + 1, u} A) X).FullSubcategory,
      Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} B) X
        ((chartEtaleScalar φ X).obj K.obj)) ∧
    (∀ K : (Etale.DerivedCategory.boundedConstructibleFiniteTor
        (ULift.{u + 1, u} A) Y).FullSubcategory,
      Etale.DerivedCategory.boundedConstructibleFiniteTor (ULift.{u + 1, u} B) Y
        ((chartEtaleScalar φ Y).obj K.obj)) :=
  sorry

/-- Ordered affine normal forms commute with arbitrary finite coefficient extension,
before chart restriction and after comparison to the pro-etale site. The last two
clauses record the zero-dimensional identity exchanges; the normal form itself uses
its canonical pullback/Tate/shift unit expansion, rather than omitting those units.

Source: Charts, coefficient compatibility of the coordinate adjunction; node Step 5.
(blueprint: lem-pur-general-field-chart-adjunction-realization).
Proof: use the finite-ctf site equivalence and its Tor bounds. On the etale site apply
the ordered right scalar normal-form equation: induct on coordinates, starting with
identity at zero. Scalar pullback composition, ordinary Tate balancing and even-shift
addition identify the recursive exchange with the single reassociation, without
permuting Tate factors. Pull back along e and use the canonical tensor symmetry which
converts right-Tate notation to left-Tate notation. Apply exact comparison pullback.
Its scalar mate is the current coefficient-representative comparison, computed on
K-flat resolutions by sectionwise balancing, so it commutes with pullback, tensor,
root balancing and shifts. Consequently the transported equation is precisely the
third displayed equality, with the actual chartScalarReassociationMap as its last
factor. At zero coordinates the ordered maps are identities; expanding the normal
form inserts the canonical pullback, tensor-unit and zero-shift maps on both sides.
This argument uses no exceptional smooth coefficient comparison. -/
theorem generalFieldChartScalarNormalForm
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} [IsNoetherian U] (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : (Etale.DerivedCategory.boundedConstructibleFiniteTor
      (ULift.{u + 1, u} A) S).FullSubcategory) :
    let φ' := RingHom.ulift.{u + 1, u + 1, u, u} φ
    let hA' := congrArg ULift.up hA
    let hB' := congrArg ULift.up hB
    let SE := fun T : Scheme.{u} ↦
      CoefficientScalarRepresentatives.extension T.smallEtaleTopology φ'
    let KB := (SE S).obj K.obj
    let CA :=
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S).mapDerivedCategory
    let CB :=
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U).mapDerivedCategory
    let JA := chartFixedSiteNormalIso (ULift.{u + 1, u} A) N hN hA' S hS d e K.obj
    let JB := chartFixedSiteNormalIso (ULift.{u + 1, u} B) N hN hB' S hS d e KB
    (chartOrderedScalarIso φ' S N hA' hB' hS d K.obj).hom ≫
        (Etale.orderedAffineRightIso (ULift.{u + 1, u} B) N hN hB' S hS d).hom.app KB =
      (SE (affineTraceTower S d)).map
          ((Etale.orderedAffineRightIso (ULift.{u + 1, u} A) N hN hA' S hS d).hom.app
            K.obj) ≫ chartOrderedScalarMap φ' N hA' hB' S d K.obj ∧
    (chartEtaleScalarIso φ' N hA' hB' hS d e K.obj).hom ≫
        (chartEtaleNormalIso (ULift.{u + 1, u} B) N hN hB' S hS d e KB).hom =
      (SE U).map
          (chartEtaleNormalIso (ULift.{u + 1, u} A) N hN hA' S hS d e K.obj).hom ≫
        chartEtaleReassociation φ' N hA' hB' (e ≫ affineTraceProjection S d) d K.obj ∧
    (chartFixedSiteScalarIso φ' U).hom.app _ ≫
        CB.map (chartEtaleScalarIso φ' N hA' hB' hS d e K.obj).hom ≫ JB.hom ≫
        (chartProOperation (ULift.{u + 1, u} B) N hB'
          (e ≫ affineTraceProjection S d) d (2 * (d : ℤ))).map
            ((chartFixedSiteScalarIso φ' S).inv.app K.obj) =
      L(sheafExtendScalars φ' U).map JA.hom ≫
        chartReassociation φ N hA hB (e ≫ affineTraceProjection S d) d (CA.obj K.obj) ∧
    (chartOrderedScalarIso φ' S N hA' hB' hS 0 K.obj).hom = 𝟙 KB ∧
      chartOrderedScalarMap φ' N hA' hB' S 0 K.obj = 𝟙 KB :=
  sorry

end AlgebraicGeometry.ProEtale.GeneralFieldChart
