/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.TowerTensorTransposeWords

/-! # Evaluation of the projection/counit transpose at one coefficient level

Source: latest blueprint, tower-geometric gamma proof (2), finite evaluation.
(blueprint: lem-sp-tensor-transpose-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTensorTranspose

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Z Y : Scheme.{u}}
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (adj : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q (SpTowerGamma.factorization j p) hF G adj)
  (hU : spConstructibleTorTowers l E Y (q.abelian Y)
    (SpTowerGamma.originalUnit l E b q Y))
  (tx : SpTowerP1.TensorData l E b X) (ty : SpTowerP1.TensorData l E b Y)

variable (n : ℕ) [Finite (SpTowerShriek.R l E n)]
  (ui : (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n
    ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩).etale ≅
    Etale.ordinaryFiniteUnit (SpTowerP1.levelRing l E n) Y)

variable (tc : SpTowerP1.TensorCoordinates l E n b X)
  (gc : SpTowerP1.GeometricCoordinates l E n (j ≫ p))

variable [IsNoetherian X] [IsNoetherian Y]
  (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
  (roots : SpCoordinateAdjunction.RootLines l E X)
  (hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
  (hY : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
  (ccX : SpTowerP1.CoefficientCoordinates l E n X hX)
  (ccY : SpTowerP1.CoefficientCoordinates l E n Y hY)
  (a : SpTowerGamma.orderedLine l E b X w d ≅ (SpTowerGamma.exceptional l E b q G).obj
    ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)
  (hQ : ∀ K : SpTowerCalculus.C l E b q Y,
    spConstructibleTorTowers l E X (q.abelian X)
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
        ((SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
          ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).obj K)))
  (hpf : ∀ K : SpTowerCalculus.C l E b q Y,
    IsIso (SpTowerShriek.projection l E b o (SpTowerGamma.factorization j p)
      ((SpTowerGamma.exceptional l E b q G).obj ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)
        ((SpTowerGamma.realization l E b q Y).obj K)))

/-- Evaluation of the actual compactification inverse-projection/counit composite,
its transpose, and its composition with the given coefficient orientation.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2), finite-level calculation.
(blueprint: lem-sp-tensor-transpose-finite-evaluation).

Proof:
1. Exact evaluation preserves the specified composite and the inverse projection.
Use tensorEvaluation and pullEvaluation of the tower calculus, with the normalized
K-flat and site coordinates, to identify its source with tensorWord. The retained
origin comparisons and counit-preserving rightAdjointUniq comparison identify the
exceptional coefficient with dualizingWord. All these comparison factors are
invertible; hence tensorWord.comparison is invertible.
2. Evaluate originalComposite. The support comparison and the realization counits
cancel. The gluing counit equation identifies its counit factor with the finite
counit. The projection evaluation equation identifies the inverse-projection
factor with the finite inverse projection. Naturality of symmetry identifies the
right-unit formula with the left-unit formula for the finite tensor-duality map.
Thus this is the inverse finite Hom equivalence applied to intrinsicTheta.
3. Evaluate the gluing unit formula for the actual adjoint transpose. The unit
compatibility in Levels, together with Step 2 and the triangle identity, gives the
WordComparison with finiteTheta. This compares explicitly constructed arrows; it
does not use faithfulness of derived evaluation.
4. Apply tensor bifunctoriality to the supplied WordComparison for the coefficient
orientation. The unit normalization equation identifies its dualizing endpoint
with that of Step 3. Compose the resulting square with Step 3. The etale composite
is gamma by its definition (tensor alpha.inv followed by the canonical tensor
mate), and the tower composite is gamma by its definition. This proves the last
WordComparison, including invertibility of its endpoint comparisons.
The calculation works for n=0 (positive exponent one), d=0, and the zero input;
none of its cancellations requires a nonzero coefficient object.
-/
theorem tensor_transpose_finite_evaluation
    (D : FiniteFieldDatum.{u}) (_hne : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [(j ≫ p).IsOver (Spec (.of D.k))] [SmoothOfRelativeDimension d (j ≫ p)]
    (dg : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)))
    (alpha : Etale.dualizingComplex
        (ModuleCat.{u + 1} (SpTowerP1.levelRing l E n)) (j ≫ p) ≅
      Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
        (SpTowerP1.levelAnnihilates l E n) X d)
    (_halpha : Etale.FiniteSmoothPurity.OrientationNormalized (SpTowerP1.levelRing l E n)
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (SpTowerP1.levelAnnihilates l E n) (j ≫ p) d dg hX alpha)
    (_hui : (SpTowerP1.nu l E n Y).map ui.hom ≫
        (SpTowerP1.unitWord l E n Y ccY).comparison =
      (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n
        ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩).comparison ≫
        (SpTowerShriek.Ev l E Y n).map
          ((SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
            (SpTowerGamma.unit l E Y)))
    (_ha : SpTowerP1.WordComparison l E n
      (SpTowerGamma.coefficientWord l E b X w roots n hX ccX tc d)
      (SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n
        ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩) a.hom
      (alpha.inv ≫ (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
    (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _ ≫
        (lv.realization n).right.map ui.inv)) :
    ∀ K : SpTowerCalculus.C l E b q Y,
      ∃ hi : IsIso (tensorWord l E b o q j p hF G adj lv hU n ui tc gc K).comparison,
      ((lv.support_evaluation n).comparison.inv.app _ ≫
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map
          (originalComposite l E b o q j p hF G adj hU tx ty K (hQ K) (hpf K)).hom =
        (((lv.adjunction n).homEquiv
          ((SpTowerGluing.level l E b q X n).obj
            (originalSource l E b o q j p G hU K (hQ K)))
          ((SpTowerGluing.level l E b q Y n).obj K)).symm
          (intrinsicTheta l E b o q j p hF G adj lv hU n ui tc gc K (hQ K) hi)).hom) ∧
      SpTowerP1.WordComparison l E n
        (tensorWord l E b o q j p hF G adj lv hU n ui tc gc K)
        (SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n K)
        (SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU K (hQ
          K) (hpf K))
        (finiteTheta l E b o q j p hF G adj lv n K) ∧
      SpTowerP1.WordComparison l E n
        (SpTowerP1.tensorWord l E n b tc
          (SpTowerP1.pullWord l E n b (o.geometry (j ≫ p)) gc
            (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n K))
          (SpTowerGamma.coefficientWord l E b X w roots n hX ccX tc d))
        (SpTowerGamma.targetWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n K)
        (SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d tx ty hF G adj hU a K (hQ
          K) (hpf K))
        (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
          (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
            (SpTowerP1.levelAnnihilates l E n) X d) alpha
          (SpTowerGamma.inputWord l E b o q (SpTowerGamma.factorization j p) hF G adj lv n K).etale
            ≫
          (SpTowerGamma.finiteRightComparison (SpTowerShriek.R l E n) j p
    (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _) := by sorry

end AlgebraicGeometry.ProEtale.SpTensorTranspose

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
