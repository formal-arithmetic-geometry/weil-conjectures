/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerTensorTransposeWords
import WeilConjectures.AlgebraicGeometry.TensorTransposeTowerNaturality
import WeilConjectures.AlgebraicGeometry.TensorTransposeFiniteEvaluation

/-! # Finite evaluation of the tower tensor transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (2).
(blueprint: lem-sp-tower-tensor-transpose-evaluation).

The maps are the published actual ordinary-tower composites in SpTowerGamma.
These definitions are imported and reused from SmoothPurityTowerGamma.
A natural index n always denotes the positive coefficient exponent n+1. Level words
retain the normalized site, scalar, tensor and adjunction comparisons.
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

/-- Naturality and exact finite evaluation of h, its actual adjunction transpose t,
and its composite with the diagonal orientation and twist reassociation.
Source: tower-geometric gamma proof (2)
(blueprint: lem-sp-tower-tensor-transpose-evaluation).

Proof:
1. Apply tensor_transpose_tower_naturality to the specified tensor-source membership
and projection-invertibility witnesses. This gives the projection/counit and
transpose naturality clauses directly in the ordinary tower category.
2. For an input arrow v, bifunctoriality of the tower tensor identifies source(v)
followed by tensor(identity,a) with tensor(identity,a) followed by tensorSource(v).
Both product arrows have components pullback(v) and a. Compose this equation with
the transpose naturality equation and associate composites. The defining formula
for gamma gives its naturality.
3. Apply tensor_transpose_finite_evaluation with the specified normalized unit,
finite coordinates and orientation comparison. Combine its per-level conjunction
with the three naturality equations. No equality is detected through evaluation.
-/
theorem tensor_transpose_evaluation
    (D : FiniteFieldDatum.{u}) (_hne : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [(j ≫ p).IsOver (Spec (.of D.k))] [SmoothOfRelativeDimension d (j ≫ p)]
    (dg : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (j ≫ p) (j ≫ p)) (pullback.diagonal (j ≫ p)))
    (alpha : Etale.dualizingComplex (SpTowerP1.levelRing l E n) (j ≫ p) ≅
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
    (∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
      (SpTowerShriek.F l E b o (SpTowerGamma.factorization j p)).map ((SpTowerGamma.tensorSource l
        E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj ⟨SpTowerGamma.originalUnit l E b q
        Y, hU⟩)).map v) ≫
          SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU
            L (hpf L) =
        SpTowerGamma.projectionCounit l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU K
          (hpf K) ≫
          (SpTowerGamma.realization l E b q Y).map v) ∧
    (∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
      (SpTowerGamma.tensorSource l E b o q (j ≫ p) ((SpTowerGamma.exceptional l E b q G).obj
        ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).map v ≫
          SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU L (hQ
            L) (hpf L) =
        SpTowerGamma.tensorMate l E b o q (SpTowerGamma.factorization j p) tx ty hF G adj hU K (hQ
          K) (hpf K) ≫
          (SpTowerGamma.exceptional l E b q G).map v) ∧
    (∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
      (SpTowerGamma.source l E b o q (j ≫ p) w d).map v ≫
          SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d tx ty hF G adj hU a L
            (hQ L) (hpf L) =
        SpTowerGamma.gamma l E b o q (SpTowerGamma.factorization j p) w d tx ty hF G adj hU a K (hQ
          K) (hpf K) ≫
          (SpTowerGamma.exceptional l E b q G).map v) ∧
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
    (lv.finite_closed n) (lv.right n) (lv.adjunction n) (lv.realization n)).inv.app _) := by
  obtain ⟨hh, ht⟩ := tensor_transpose_tower_naturality l E b o q j p
    hF G adj hU tx ty hQ hpf
  refine ⟨hh, ht, ?_, ?_⟩
  · intro K L v
    let T := SpTowerShriek.tensor l E b X
    have ha : (SpTowerGamma.source l E b o q (j ≫ p) w d).map v ≫
        T.map (Prod.mkHom (𝟙 _) a.hom) =
      T.map (Prod.mkHom (𝟙 _) a.hom) ≫
        (SpTowerGamma.tensorSource l E b o q (j ≫ p)
          ((SpTowerGamma.exceptional l E b q G).obj
            ⟨SpTowerGamma.originalUnit l E b q Y, hU⟩)).map v := by
      dsimp only [SpTowerGamma.source, SpTowerGamma.tensorSource,
        Functor.comp_map, Prod.sectL_map]
      rw [← T.map_comp, ← T.map_comp]
      congr 1
      exact Prod.hom_ext (by simp) (by simp)
    dsimp only [SpTowerGamma.gamma]
    rw [reassoc_of% ha, ht K L v, Category.assoc]
  · exact tensor_transpose_finite_evaluation l E b o q j p hF G adj lv hU tx ty
      n ui tc gc w d roots hX hY ccX ccY a hQ hpf D _hne dg alpha _halpha _hui _ha

end AlgebraicGeometry.ProEtale.SpTensorTranspose

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
