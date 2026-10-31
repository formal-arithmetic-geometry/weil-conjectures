/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerTensorTransposeWords

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

/-- Finite evaluation word comparisons for a supplied endpoint witness.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2).
These are clauses (ii) and (iii) of `tensor_transpose_finite_evaluation`; `IsIso` is a
proposition, so the witness is the one of `tensor_transpose_finite_evaluation_core`.
Proof: fix `K` and the witness `hi`.
4. The adjunction formula gives `t_K = G(h_K) ∘ η_{Q(K)}`. The level comparisons of `lv` preserve
unit and counit (tower gluing (3)), so the finite Hom equivalence applied to the evaluated
equation of `tensor_transpose_finite_evaluation_core` (clause (i)) computes the evaluation of
`t_K` as `intrinsicTheta K hi`. Substituting the definition of `intrinsicTheta` and cancelling
each comparison with its inverse leaves
`c_{W(K)} ≫ Ev_{X,n}(tensorMate K) = ν_X(finiteTheta K) ≫ c_{T(K)}`; with the endpoint
isomorphisms `hi` and the target comparison this is the first WordComparison. No inference from
equality of levels to equality of tower morphisms is used.
5. The orientation-word normalization lemma with `W = C`, `s = a`, `t = alpha⁻¹`, whose hypothesis
is `_ha`, gives `WordComparison(C, dualizingWord, a, alpha⁻¹)`. Tensoring with the identity square
on `pullWord (inputWord K)` gives, by the recursive tensor comparison and bifunctoriality, the
square from `S(K)` to `W(K)` with upper map `1 ⊗ a` and lower map `1 ⊗ alpha⁻¹`. Pasting with
step 4: the upper composite is the tower `gamma`, the lower one is
`(1 ⊗ alpha⁻¹) ≫ θ ≫ v⁻¹ = γ_{f,R_n}(K_n) ≫ v⁻¹` by the finite canonical-map definition. This is
the second WordComparison, its endpoints being invertible by step 4 and `_ha`.
(blueprint: lem-route-tensor-transpose-finite-evaluation-words). -/
theorem tensor_transpose_finite_evaluation_words
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
    ∀ K : SpTowerCalculus.C l E b q Y,
      IsIso (tensorWord l E b o q j p hF G adj lv hU n ui tc gc K).comparison →
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
