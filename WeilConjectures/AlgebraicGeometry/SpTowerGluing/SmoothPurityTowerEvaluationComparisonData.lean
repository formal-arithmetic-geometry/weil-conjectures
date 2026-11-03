/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerFiniteLevelData

/-! # Finite comparisons for evaluated smooth-purity tower adjunctions

The finite comparison interface is strictly below `EvaluationLevelData`: it omits
the quotient-transition reduction equations.
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

/-- Evaluated comparisons and the two adjunction equations, with reductions omitted.
Source: blueprint det-sp-tower-gluing, *Levels*: evaluation at level $n$ of the tower right
adjoint represents the finite functor, compatibly with counits, hence with units.

Proof. Write $F_n=Rf_{!,R_n}$ ($R_n=\mathcal O_E/\ell^{n+1}$), $J_n$ = `finite.right n`,
$a_n$ = `(support_evaluation n).comparison` (by its `normalization` field it equals
`charts.calculus.finite.evaluation _ n`), $H_n=e_{X,n}GK$, $K_n=e_{Y,n}K$ and
$\gamma_n=e_{Y,n}(\varepsilon_K)\circ a_n(GK)^{-1}:F_nH_n\to K_n$.
1. $X,Y$ are of finite type; lem-sp-smooth-admissible-coordinate-cover gives a finite
admissible coordinate cover of $X$ (possibly empty), and every nonempty intersection $W$
satisfies the chart hypotheses (étale/separated/quasi-compact permanence).
2. On each $W$ the normalized `ConstructionAt` of `charts` has a finite adjunction on all finite
$R_n$-ctf objects; evaluating `Charts.comparison` and `Charts.counit` and using the étale and
open normalizations of the calculus identifies its counit with $\gamma_n|_W$.
lem-sp-finite-ring-counit-local-representability then gives that
$u\mapsto\gamma_n\circ F_n(u):\operatorname{Hom}(P,H_n)\to\operatorname{Hom}(F_nP,K_n)$ is bijective
for every finite ctf $P$ on $X$.
3. Let $\rho_n(K):H_n\to J_nK_n$ be the `finite.adjunction n` transpose of $\gamma_n$; this is
the `counit` equation. Step 2 at $P=J_nK_n$ gives an inverse. Tower counit naturality and
naturality of $a_n$, transposed, make $\rho_n$ natural in $K$: this is `comparison n`.
4. The transpose of $e_{X,n}(\eta_M)$ followed by `comparison` and $J_n(a_n(M))$ is, by the
counit equation and naturality of $a_n$,
$a_n(M)\circ e_{Y,n}(\varepsilon_{FM}\circ F\eta_M)\circ a_n(M)^{-1}=1$
(tower triangle identity), the transpose of the finite unit: this is `unit`.
(blueprint: lem-route-tower-evaluation-level-comparison-data). -/
structure EvaluationLevelComparisonData (k : Type u) [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    {f : X ⟶ Y} (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q c hF ⊣ G)
    (finite : FiniteLevelData l E b o q c hF)
    (support_evaluation : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q c n) where
  comparison : ∀ n : ℕ, G ⋙ level l E b q X.left n ≅
    level l E b q Y.left n ⋙ finite.right n
  counit : ∀ (n : ℕ) (K : SpTowerCalculus.C l E b q Y.left),
    (support_evaluation n).comparison.inv.app (G.obj K).obj ≫
        (spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).map
          (adj.counit.app K).hom =
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
        ((comparison n).hom.app K).hom ≫
      ((finite.adjunction n).counit.app ((level l E b q Y.left n).obj K)).hom
  unit : ∀ (n : ℕ) (M : SpTowerCalculus.C l E b q X.left),
    (spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).map
        (adj.unit.app M).hom ≫
        ((comparison n).hom.app ((support l E b o q c hF).obj M)).hom ≫
      ((finite.right n).map (ObjectProperty.homMk
        ((support_evaluation n).comparison.hom.app M.obj))).hom =
      ((finite.adjunction n).unit.app ((level l E b q X.left n).obj M)).hom

/-- Existence of the evaluated finite comparison interface.
Source and proof: see `EvaluationLevelComparisonData`
(blueprint: lem-route-tower-evaluation-level-comparison-data). -/
theorem evaluationLevelComparisonData_exists
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
        (CondensedRing.compactificationOverField f) n) :
    Nonempty (EvaluationLevelComparisonData l E b o q k
      (CondensedRing.compactificationOverField f) hF G adj finite support_evaluation) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
