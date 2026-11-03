/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerEvaluationComparisonData

/-! # Reduction coherence for evaluated smooth-purity tower adjunctions

The reduction interface is strictly below `EvaluationLevelData`: the comparison family is
supplied as a parameter, and the `reduction` field assumes its counit equation (the `counit`
field of `EvaluationLevelComparisonData`). That hypothesis is essential: it pins each
`comparison n` as the finite transpose of the evaluated tower counit. For an arbitrary family
of isomorphisms the reduction equation is false (keep `comparison n` and twist `comparison m`
by a unit of $R_m$ different from `1`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Quotient-transition coherence for an already constructed evaluated comparison.
Source: blueprint det-sp-tower-gluing, *Levels*, last two sentences (the transition maps
of the tower right adjoint are the coefficient comparisons $c_{n,m}$ of
det-sp-reduction-exceptional).

Proof. Write $F_n=Rf_{!,R_n}$, $J_n$ = `finite.right n`,
$a_n$ = `(support_evaluation n).comparison`,
$H_n=e_{X,n}GK$, $K_n=e_{Y,n}K$, $\gamma_n=e_{Y,n}(\varepsilon_K)\circ a_n(GK)^{-1}$ and
$\rho_n$ = `(comparison n).hom.app K`; the counit hypothesis `hcounit` of `reduction` says
$\varepsilon^n_{K_n}\circ F_n(\rho_n)=\gamma_n$. By its `normalization` field, $a_n$ equals
`charts.calculus.finite.evaluation _ n`, the evaluation the reduction calculus is stated for.
1. Fix $m\le n$, $S_T=(-)\otimes^L_{R_n}R_m$, $r^K:S_YK_n\to K_m$, $r^{GK}:S_XH_n\to H_m$.
The reduction fields of `charts.calculus.reduction` give
$a_m(GK)\circ r^{FGK}=F_m(r^{GK})\circ b(H_n)\circ S_Y(a_n(GK))$ with $b(H_n)$ invertible,
and naturality at $\varepsilon_K$ gives
$r^K\circ S_Y(e_{Y,n}\varepsilon_K)=e_{Y,m}(\varepsilon_K)\circ r^{FGK}$.
Substituting, $\gamma_m\circ F_m(r^{GK})=r^K\circ S_Y(\gamma_n)\circ b(H_n)^{-1}$ (*).
2. By definition of `coefficientMate`,
$\varepsilon^m_{S_YK_n}\circ F_m(c_{n,m})=S_Y(\varepsilon^n_{K_n})\circ b(J_nK_n)^{-1}$.
The $F_m\dashv J_m$ transposes of $u=\rho_m\circ r^{GK}$ and
$v=J_m(r^K)\circ c_{n,m}\circ S_X(\rho_n)$ are both $r^K\circ S_Y(\gamma_n)\circ b(H_n)^{-1}$:
for $u$ by `hcounit` and (*); for $v$ by counit naturality, the definition of
$c_{n,m}$, naturality of $b$, and `hcounit` at level $n$. Injectivity of transposition
gives $u=v$. Equal indices use the scalar unitor, quotient chains the scalar associator;
the empty source and $d=0$ need no change; no flatness of $R_n\to R_m$ is used.
(blueprint: lem-route-tower-evaluation-level-reduction-data). -/
structure EvaluationLevelReductionData (k : Type u) [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    {f : X ⟶ Y} (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q c hF ⊣ G)
    (finite : FiniteLevelData l E b o q c hF)
    (support_evaluation : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q c n)
    (comparison : ∀ n : ℕ,
      G ⋙ level l E b q X.left n ≅ level l E b q Y.left n ⋙ finite.right n) where
  reduction : ∀ (_hcounit : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Y.left),
      (support_evaluation n).comparison.inv.app (G.obj K).obj ≫
          (spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).map
            (adj.counit.app K).hom =
        (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
          ((comparison n).hom.app K).hom ≫
        ((finite.adjunction n).counit.app ((level l E b q Y.left n).obj K)).hom)
    (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y.left),
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X.left).map
        ((comparison n).hom.app K).hom ≫
      (coefficientMate l E b c m n h (finite.finite_closed n) (finite.finite_closed m)
        (finite.scalarX m n h) (finite.scalarY m n h) (finite.right n) (finite.right m)
        (finite.adjunction n) (finite.adjunction m)
        ((level l E b q Y.left n).obj K)
        (finite.direct_image_iso m n h ((level l E b q Y.left n).obj K))).hom ≫
      ((finite.right m).map (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E Y.left (q.abelian Y.left) h (q.scalar Y.left h)
          K.obj))).hom =
    SpTowerCalculus.reduction l E X.left (q.abelian X.left) h (q.scalar X.left h)
        (G.obj K).obj ≫ ((comparison m).hom.app K).hom

/-- Existence of the evaluated reduction-coherence interface.
Source and proof: see `EvaluationLevelReductionData`
(blueprint: lem-route-tower-evaluation-level-reduction-data). -/
theorem evaluationLevelReductionData_exists
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G)
    (charts : Charts l E b o q k X Y
      ⟨inferInstance, inferInstance, inferInstance⟩ f d
      (CondensedRing.compactificationOverField f) hF G adj)
    (finite : FiniteLevelData l E b o q (CondensedRing.compactificationOverField f) hF)
    (support_evaluation : ∀ n : ℕ,
      SpTowerCalculus.Evaluation l E b o q
        (CondensedRing.compactificationOverField f) n)
    (comparison : ∀ n : ℕ,
      G ⋙ level l E b q X.left n ≅
        level l E b q Y.left n ⋙ finite.right n) :
    Nonempty
      (EvaluationLevelReductionData l E b o q k
        (CondensedRing.compactificationOverField f) hF G adj finite
        support_evaluation comparison) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
