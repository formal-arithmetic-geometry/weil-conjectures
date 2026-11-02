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
