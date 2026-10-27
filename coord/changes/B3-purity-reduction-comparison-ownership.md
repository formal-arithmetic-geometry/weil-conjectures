# Purity reduction comparison ownership

## Reason

The two actual coefficient-transport steps need the existing source and target
comparison definitions. Their statements cannot import their parent theorem without
an import cycle. Move the four definitions, with verbatim signatures and bodies,
into Sheaf.Paper.PurityTowerReductionComparisons and publicly re-export that module
from Sheaf.Paper.PurityConjugatesTowerReduction. This is argument decomposition,
not a compilation-time split. No mathematical definition changes.

## Old

In Sheaf.Paper.PurityConjugatesTowerReduction:

```lean
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [b : SpTowerShriek.Base l E] (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The actual levelwise derived pullback, Tate twist, and even shift, transported
back to the original ordinary derived category of strict towers.
Source: gamma proof (3) (blueprint: lem-sp-purity-conjugates-tower-reduction). -/
def pullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
    (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
    ((SpTowerGamma.source l E b o q f w d).obj K)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (w : SpChartAdmissibility.Twists l E X) (d : ℕ)
  (hF : ∀ M : SpTowerCalculus.C l E b q X,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((SpTowerCalculus.F l E b o q c).obj M.obj))
  (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
  (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
  (lv : SpTowerGluing.Levels l E b o q c hF G adj)
  (roots : SpCoordinateAdjunction.RootLines l E X)
  (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
  (cc : ∀ n : ℕ, SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
  (tc : ∀ n : ℕ, SpTowerP1.TensorCoordinates l E n b X)
  (gc : ∀ n : ℕ, SpTowerP1.GeometricCoordinates l E n f)

/-- The fixed pullback/tensor evaluation word of the purity source. It uses the
retained etale origin, root generators, and normalized K-flat tensor comparisons.
Source: gamma proof (3) (blueprint: lem-sp-purity-conjugates-tower-reduction). -/
def sourceWord (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :=
  SpTowerP1.tensorWord l E n b (tc n)
    (SpTowerP1.pullWord l E n b (o.geometry f) (gc n)
      (SpTowerGamma.inputWord l E b o q c hF G adj lv n K))
    (SpTowerGamma.coefficientWord l E b X w roots n (unitsX n) (cc n) (tc n) d)

/-- The canonical source comparison in the original strict-tower evaluation.
It includes the realization counit and the prescribed evaluation comparison.
Source: gamma proof (3) (blueprint: lem-sp-purity-conjugates-tower-reduction). -/
def sourceComparison (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :=
  (sourceWord l E o q c w d hF G adj lv roots unitsX cc tc gc n K).comparison ≫
    (SpTowerShriek.Ev l E X n).map
      ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.inv.app
        ((SpTowerGamma.source l E b o q f w d).obj K)) ≫
    (SpTowerCalculus.levelComparison l E b q X n).hom.app
      (pullbackTower l E o q f w d K)

/-- The exceptional-output comparison, using the finite right adjoint's actual
counit-normalized realization and the glued evaluation comparison.
Source: gamma proof (3) (blueprint: lem-sp-purity-conjugates-tower-reduction). -/
def targetComparison (n : ℕ) (K : SpTowerCalculus.C l E b q Y) :=
  (SpTowerGamma.targetWord l E b o q c hF G adj lv n K).comparison ≫
    (SpTowerCalculus.levelComparison l E b q X n).hom.app (G.obj K).obj
```

The four bodies are preserved byte for byte in the new module.

Original public imports in the parent:

```lean
public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.SecSmoothPurity.ReductionCompatibilities
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
```

## New

The same declarations, signatures and bodies in
Sheaf.Paper.PurityTowerReductionComparisons, re-exported by the original module.
The parent's public import is now:

```lean
public import Sheaf.Paper.PurityTowerReductionComparisons
```

The new owner publicly imports SmoothPurityTowerGamma and
FiniteSmoothCoefficientArrows. The parent uses private proof imports for
FiniteGeneralRingOrientation, SmoothTensorDuality and the two transport lemmas,
as well as its existing bounds and Tor-transport imports. Its removed public
imports are recorded in report.md; there are no current importers to adapt.

The new definition owner is def-sp-purity-reduction-comparisons. The parent node
keeps its two theorem attachments and its statement unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.PurityConjugatesTowerReduction --uses
pullbackTower sourceWord sourceComparison targetComparison` found no downstream
modules. The parent is the only existing Lean user. DAG parents with unfinished
proofs continue to use its unchanged statements and all names remain re-exported.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurityConjugatesTowerReduction | B3 | Import new owner; original public names preserved. |
| Sheaf.Paper.PurityTowerReductionComparisons | new, B3 | Own the four identical definitions. |
| Sheaf.Paper.PurityPullbackReductionTransport | new, B3 | State actual source reduction transport. |
| Sheaf.Paper.PurityFiniteReductionTransport | new, B3 | State finite purity/output transport. |

No target statement or definition body changes. There are no forced adaptations.

## Status

landed 20261025T201344-L-2447557 2026-10-25 (merge of deliver/B3/Sheaf.Paper.PurityConjugatesTowerReduction)
