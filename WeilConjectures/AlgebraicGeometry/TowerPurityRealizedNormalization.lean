/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerPurityRealizedData

/-! # Normalization square for realized integral purity

Source: latest blueprint, tower-geometric-gamma.proof.md, Clause (2),
steps 2--6 and finite-coefficient normalization in Clause (1).
(blueprint: lem-pur-realized-tower-purity-normalization).

The conclusion concerns the reduction of the projection word, rather than the
integral purity adjunct. Its other square is naturality in an arbitrary second
input morphism. Transposition of tower gamma and reconstruction are separate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.IntegralSystemRealization
namespace AlgebraicGeometry.ProEtale.RealizedTowerPurity

/-- Simultaneous normalization of coefficient models and the projection word.
Source: current blueprint, tower-geometric-gamma.proof.md, Clause (2), the
completed-operation substitution and projection-reduction calculations, and
Clause (1), finite orientations
(blueprint: lem-pur-realized-tower-purity-normalization).

Proof: use the reconstruction comparisons to obtain the realized adjunction and
restrict its two functors to the common finite-Tor category. For compact support,
finite quotient base change and the cohomological dimension bound preserve one
common Tor interval. For its right adjoint, the tower purity comparison transfers
the twisted-pullback interval, and cofinal quotient reassociation transfers it to
every uniformizer quotient. Choose all operation models simultaneously, with
K-flat tensor comparisons and pullback maps normalized by the Roos augmentation.
Write ell = u*pi^e and restrict the uniformizer systems to e(n+1); use the actual
cofinal limit comparison on objects, maps and both augmentations. Combine the
canonical twisted-pullback source comparison with the ordered Tate-line tensor
comparison to select r.sourceComparison. Tensor-unit multiplication gives muX,
muY and the two displayed K-flat unit normalizations. The flat Tate-line tensor
model gives s and its SourceNormalized equation on every flat representative.
The normalized left proper/open comparison, its adjoint mate and the finite
site-comparison Hom chain give S, normal and e. Reduce these actual maps: the
finite source comparison, diagonal orientation and counit mates identify their
composite with the finite purity arrow, including exponent one and d=0.

For the projection square, apply compactification_b_projection_reduction with
its pinned b and the same models, first on the Tate line and then on the
exceptional image of the coefficient unit. The first is finite Tor; the second
is isomorphic to it by realized purity at the unit. Thus the completion units
and reassociation in the statement are invertible. The normalized source/unit
comparison identifies reduction of the unit purity component with the diagonal
tower orientation: at the unit, the proper projection is the counit triangle,
and the open factor is the unit tensor normalization. Move the reconstruction
counit across inverse projection by naturality, substitute its specified counit
reduction, and use the primitive tensor/pullback comparisons. This gives exactly
towerProjection, whose last factor is the tower projection/counit word, before
transposing gamma. Finally, projection naturality in any second-input morphism a
passes through the two invertible completion units. Compose with the inverse
projections to obtain the last square. All these calculations take place on
entire systems; finite evaluations are used only for the separately displayed
finite-purity comparisons. No integral equality is deduced from evaluations. -/
theorem realized_tower_purity_normalization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (b : SpTowerShriek.Base C.l E) (o : SpTowerShriek.Operations C.l E b)
    (q : SpTowerCalculus.Coordinates C.l E b)
    (w : SpChartAdmissibility.Twists C.l E X)
    (RX : SpReductionTower C.l E X (q.abelian X))
    (NX : SpNormalizedEquivalence C.l E X (q.abelian X) RX)
    (RY : SpReductionTower C.l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence C.l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C C.l E b q X,
      spConstructibleTorTowers C.l E Y (q.abelian Y)
        ((SpTowerCalculus.F C.l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (Gb : SpTowerCalculus.C C.l E b q Y ⥤ SpTowerCalculus.C C.l E b q X)
    (ab : SpTowerGluing.support C.l E b o q (SpTowerGamma.factorization j p) hF ⊣ Gb)
    (lv : SpTowerGluing.Levels C.l E b o q (SpTowerGamma.factorization j p) hF Gb ab) :
    ∃ (r : SpIntegralAdjunction.Realization C.l E b o q j p d w RX NX RY NY hF Gb ab lv)
      (hP : ∀ M : finiteTorConstructibleIntegralCategory C.l E X,
        finiteTorConstructibleIntegral C.l E Y
          ((CompleteCompactificationLimit.image C.l E
            (SpTowerGamma.factorization j p)).obj M.obj))
      (hH : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
        finiteTorConstructibleIntegral C.l E X
          ((SpIntegralAdjunction.right C.l E b q RX NX RY r.reductionY Gb r.closed).obj
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)).obj)
      (m : CompleteProjectionDescent.DescentModels C.l E)
      (S : ConstructibleExceptionalCoefficients.RingSystem
        C.l C.Qbar D C.different (f := j ≫ p))
      (normal : WeilConjectures.RealizedTowerPurity.FiniteNormalization
        D C E (j ≫ p) S (SpTowerGamma.factorization j p))
      (core : CompletedUnitPullback.Core C.l E (j ≫ p))
      (muX : integralConstantCoefficientObject C.l E X ≅
        (calculus C.l E X).integralClosed.monoidal.tensorUnit)
      (muY : integralConstantCoefficientObject C.l E Y ≅
        (calculus C.l E Y).integralClosed.monoidal.tensorUnit),
    letI := r.noetherianX
    letI := r.noetherianY
    (∃ hX : (PurUnitTrace.unitComplex D C E X).IsKFlatIndependentCoefficients,
      PurUnitTrace.IsUnitNormalized D C E X hX muX) ∧
    (∃ hY : (PurUnitTrace.unitComplex D C E Y).IsKFlatIndependentCoefficients,
      PurUnitTrace.IsUnitNormalized D C E Y hY muY) ∧
    ∀ (G : finiteTorConstructibleIntegralCategory C.l E Y ⥤
        finiteTorConstructibleIntegralCategory C.l E X)
      (adj : support C.l E (SpTowerGamma.factorization j p) hP ⊣ G),
      (∃ (e : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
          (G.obj K).obj ≅ purAdicTarget D C E (j ≫ p) K.obj)
        (s : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
          purAdicSource D C E (j ≫ p) d K.obj ≅
            (SpTwistedPullback.source C.l E (j ≫ p) (d : ℤ) (2 * (d : ℤ))).obj
              ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)),
        (∃ hL : ((CochainComplex.singleFunctor (scalarReductionSource C.l E X) 0).obj
            (integralTwistLine C.l E X (d : ℤ))).IsKFlatIndependentCoefficients,
          WeilConjectures.RealizedTowerPurity.SourceNormalized D C E (j ≫ p) d hL s) ∧
        (∀ (K : finiteTorConstructibleIntegralCategory C.l E Y) (n : ℕ),
          (scalarReductionDerivedExtension C.l E X n).map (e K).hom ≫
              purAdicTargetReduction D C E (j ≫ p) d K.obj K.property n =
            (scalarReductionDerivedExtension C.l E X n).map
              (((WeilConjectures.RealizedTowerPurity.specifiedAdjunction D C E
                (j ≫ p) S (SpTowerGamma.factorization j p) hP).rightAdjointUniq
                  adj).inv.app K).hom ≫
              WeilConjectures.RealizedTowerPurity.finiteReduction D C E (j ≫ p) S
                (SpTowerGamma.factorization j p) normal K n) ∧
        ∀ (K : finiteTorConstructibleIntegralCategory C.l E Y) (n : ℕ),
          (scalarReductionDerivedExtension C.l E X n).map
              ((s K).hom ≫ component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G adj K ≫
                (e K).hom) ≫
              purAdicTargetReduction D C E (j ≫ p) d K.obj K.property n =
            purAdicSourceReduction D C E (j ≫ p) d K.obj K.property n ≫
              (purAdicFiniteArrow D C E (j ≫ p) d K.obj K.property n).hom) ∧
      (∀ (K : finiteTorConstructibleIntegralCategory C.l E Y),
        ∃ (hvT : IsIso (CompactificationBProjection.sourceUnit C.l E m
            (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E
              X d)))
        (hhT : IsIso (CompactificationBProjection.innerUnit C.l E m
            (j ≫ p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E X d)))
        (hvW : IsIso (CompactificationBProjection.sourceUnit C.l E m
            (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l
              E Y, core.admissibleY.1⟩).obj)))
        (hhW : IsIso (CompactificationBProjection.innerUnit C.l E m
            (j ≫ p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l E Y,
              core.admissibleY.1⟩).obj)))
        (hu : IsIso (((m.integral.tensor Y).chi C.l E).app
          (K.obj, integralConstantCoefficientObject C.l E Y))),
        IsIso (WeilConjectures.RealizedTowerPurity.reassociation C.l E (j ≫ p) d m.integral
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) ∧
        ∀
        (hpT : IsIso (CompactificationBProjection.alpha C.l E m
            (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E
              X d)
            (@asIso _ _ _ _ (CompactificationBProjection.sourceUnit C.l E m
              (SpTowerGamma.factorization j p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l
                E X d)) hvT)
            (@asIso _ _ _ _ (CompactificationBProjection.innerUnit C.l E m
              (j ≫ p) K.obj (WeilConjectures.RealizedTowerPurity.line C.l E X d)) hhT)))
        (hpW : IsIso (CompactificationBProjection.alpha C.l E m
            (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l
              E Y, core.admissibleY.1⟩).obj)
            (@asIso _ _ _ _ (CompactificationBProjection.sourceUnit C.l E m
              (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject
                C.l E Y, core.admissibleY.1⟩).obj)) hvW)
            (@asIso _ _ _ _ (CompactificationBProjection.innerUnit C.l E m
              (j ≫ p) K.obj ((G.obj ⟨integralConstantCoefficientObject C.l E Y,
                core.admissibleY.1⟩).obj)) hhW))),
        reduceWord C.l E b o q j p d w RX NX RY NY hF Gb ab lv r K
          ((CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
            (WeilConjectures.RealizedTowerPurity.reassociation C.l E (j ≫ p) d m.integral
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K)) ≫
          (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
            ((integralCompletedTensor C.l E X).map (Prod.mkHom (𝟙 ((integralDerivedPullback C.l E
              (j ≫ p)).obj K.obj)) ((WeilConjectures.RealizedTowerPurity.sourceUnit C.l E (j ≫ p)
                d core muX).inv ≫ component C.l E b o q j p d w RX NX RY NY hF Gb ab lv r hH hP G
                  adj ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩))) ≫
          WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
              (SpTowerGamma.factorization j p) K.obj ((G.obj ⟨integralConstantCoefficientObject
                C.l E Y, core.admissibleY.1⟩).obj) hvW hhW hpW ≫
          (integralCompletedTensor C.l E Y).map (Prod.mkHom (𝟙 K.obj) (adj.counit.app
            ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩).hom) ≫
          WeilConjectures.RealizedTowerPurity.rightUnit C.l E Y m.integral muY K.obj hu) =
          towerProjection C.l E b o q j p d w RX NX RY NY hF Gb ab lv r
            ((PurCompactSupport.finiteTorIntegralInclusion C.l E Y).obj K) ∧
        ∀ a : WeilConjectures.RealizedTowerPurity.line C.l E X d ⟶
            (G.obj ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩).obj,
          (CompleteProjectionDescent.integralImage C.l E (SpTowerGamma.factorization j p)).map
              ((integralCompletedTensor C.l E X).map
                (Prod.mkHom (𝟙 ((integralDerivedPullback C.l E (j ≫ p)).obj K.obj)) a)) ≫
            WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
              (SpTowerGamma.factorization j p) K.obj
              ((G.obj ⟨integralConstantCoefficientObject C.l E Y, core.admissibleY.1⟩).obj)
              hvW hhW hpW =
          WeilConjectures.RealizedTowerPurity.inverseProjection C.l E m
              (SpTowerGamma.factorization j p) K.obj
              (WeilConjectures.RealizedTowerPurity.line C.l E X d) hvT hhT hpT ≫
            (integralCompletedTensor C.l E Y).map
              (Prod.mkHom (𝟙 K.obj)
                ((CompleteProjectionDescent.integralImage C.l E
                  (SpTowerGamma.factorization j p)).map a))) := by
  sorry


end AlgebraicGeometry.ProEtale.RealizedTowerPurity
