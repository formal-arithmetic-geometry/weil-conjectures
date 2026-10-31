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

/-- Finite evaluation core: the evaluated compactification composite is the finite
adjoint transpose.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2).
This is clause (i) of `tensor_transpose_finite_evaluation`, together with its endpoint witness.
Proof: fix `K`.
1. By the word construction, `tensorWord K` is the tensor word of `pullWord (inputWord K)` with
`dualizingWord`, and the comparison of `dualizingWord` is
`ν_X(f^!(u⁻¹) ≫ v⁻¹ ≫ r_n(ui⁻¹)) ≫ c_{T(U)}`. Every factor is invertible (`u`, `ui`, `v` are
isomorphisms, functors preserve inverses, the retained target-word comparison is invertible); the
recursive pull comparison uses the natural isomorphism of `gc` and the recursive tensor comparison
that of `tc`. Hence `tensorWord.comparison` is invertible: this is the witness `hi`. No
invertibility of θ or γ and no faithfulness of evaluation is used.
2. Expand the realization lift defining `originalComposite` and precompose its evaluation with
`s_{n,Q(K)}⁻¹`. The support comparison and realization counits cancel against their inverse
comparison factors. The strict compactification realization comparison identifies the evaluated
projection with the finite compactification projection, and `hpf K` makes it invertible, so its
inverse is identified too. The signed symmetry and scalar unitors fixed by `tx`, `ty`, `tc`
evaluate to the finite ones on K-flat representatives. The counit factor is identified by the
unit/counit compatibility of `lv` (tower gluing (3)), with the geometric-adjunction and
open-unit evaluation equations inside the compactification presentation. The equation `_hui`
identifies the evaluated realization of `U` with the finite coefficient unit. The finite arrow is
thus `β ≫ P⁻¹ ≫ β ≫ (1 ⊗ ε_𝟙) ≫ ρ`.
3. The smooth tensor theorem with `A = R_n`, `N = ℓ^(n+1)` (finite, `N • A = 0`, `N > 0`, `Y`
Noetherian with `N` invertible, `f` smooth separated compactifiable of pure dimension `d`) says
that the finite adjoint transpose of this arrow is `θ_{f,K_n}`; the canonical-map definition
relates the dualizing complex and `f^! R_{n,Y}[0]` by `f^!(u⁻¹)`. Since `v` preserves counits,
`finiteTheta K = θ_{f,K_n} ≫ v⁻¹`, and `intrinsicTheta K hi` is that map conjugated by the listed
comparisons, applying the inverse finite Hom equivalence gives the stated equation.
The argument covers `n = 0`, `d = 0` and `K = 0`.
(blueprint: lem-route-tensor-transpose-finite-evaluation-core). -/
theorem tensor_transpose_finite_evaluation_core
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
      ∃ hi : IsIso (tensorWord l E b o q j p hF G adj lv hU n ui tc gc K).comparison,
      ((lv.support_evaluation n).comparison.inv.app _ ≫
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map
          (originalComposite l E b o q j p hF G adj hU tx ty K (hQ K) (hpf K)).hom =
        (((lv.adjunction n).homEquiv
          ((SpTowerGluing.level l E b q X n).obj
            (originalSource l E b o q j p G hU K (hQ K)))
          ((SpTowerGluing.level l E b q Y n).obj K)).symm
          (intrinsicTheta l E b o q j p hF G adj lv hU n ui tc gc K (hQ K) hi)).hom) := by sorry

end AlgebraicGeometry.ProEtale.SpTensorTranspose
