/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerFiniteLevelData

/-! # Evaluated tower comparisons and their reduction coherence

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md, *Levels*: evaluation at level $n$ of the tower right
adjoint represents the finite functor, and the transition maps are the coefficient comparisons
(blueprint: lem-route-tower-evaluation-level-data).
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

/-- The tower-evaluation fields of `Levels` after finite data is fixed.
This is strictly lower than `Levels`: it contains only normalized evaluations,
finite comparisons, and their unit/counit/reduction equations.
Source: blueprint det-sp-tower-gluing, *Levels* (blueprint: lem-route-tower-evaluation-level-data).
-/
structure EvaluationLevelData (k : Type u) [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    {f : X ⟶ Y} (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q c hF ⊣ G)
    (finite : FiniteLevelData l E b o q c hF) where
  support_evaluation : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q c n
  comparison : ∀ n : ℕ, G ⋙ level l E b q X.left n ≅ level l E b q Y.left n ⋙ finite.right n
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
  reduction : ∀ (m n : ℕ) (h : m ≤ n) (K : SpTowerCalculus.C l E b q Y.left),
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
    SpTowerCalculus.reduction l E X.left (q.abelian X.left) h (q.scalar X.left h) (G.obj K).obj ≫
      ((comparison m).hom.app K).hom

/-- The evaluated tower data exists once the finite exceptional data and normalized charts
are supplied.
Source: blueprint det-sp-tower-gluing, *Levels*, last paragraph
(blueprint: lem-route-tower-evaluation-level-data).

Proof:
1. Evaluation at level $n$ is exact and commutes with the compact-support operations by
[det-sp-tower-shriek-levels]; this is the normalized evaluation `support_evaluation n`.
2. For each $K$ the chart comparisons of `charts` and their counit equations evaluate to the
finite local counits. Repeating the gluing argument of det-sp-tower-gluing after evaluation (the
finite-cover induction applies to EVERY finite ctf test object, not only to those lifting to a
tower) shows that $((G K)_n,\varepsilon_n)$ represents
$\operatorname{Hom}(Rf_{!,A_n}-,K_n)$ on finite ctf objects. The finite adjunction
`finite.adjunction n` represents the same functor, whichever right adjoint was chosen; comparing
the two counits by transposition gives inverse arrows, i.e. `comparison n`, and exactly the
equation `counit`.
3. Evaluating the tower counit naturality for $K\to L$ and injectivity of the finite transpose
make the comparisons natural in $K$. Evaluating the tower triangle identity identifies the tower
unit with the finite unit: the equation `unit`. Faithfulness of derived evaluation is not used.
4. The tower reduction map of $G K$ and $f^!$ of the reduction map of $K$ are both determined by
their counit transposes. The coefficient comparison $c_{n,m}$ of [det-sp-reduction-exceptional]
is the counit transpose `coefficientMate` of $b^{-1}\circ S_Y(\varepsilon_n)$ for the finite
adjunctions of `finite`; it has the same chart description as the tower transition. Transporting
the transposes along the counit-preserving comparisons of steps 2-3 gives `reduction`. Equal
indices use the scalar unitor, a chain of quotient maps the scalar associator. The empty source
and $d=0$ need no change. -/
theorem evaluationLevelData_exists
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
    (finite : FiniteLevelData l E b o q (CondensedRing.compactificationOverField f) hF) :
    Nonempty (EvaluationLevelData l E b o q k
      (CondensedRing.compactificationOverField f) hF G adj finite) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
