# AlgebraicGeometry.Scheme.completedProperIndependentOrigins

## Reason

Close the theorem from the existing strict normalization and direct-image interfaces.
Remove unused and redundant public and proof imports. The theorem's signature and
visibility are unchanged. In particular, remove the import of the compact-support
construction: this proper factor does not need compactifications or open shriek.

## Old

The declaration signature was:

```lean
theorem completedProperIndependentOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f] :
    (∀ (H H' : d.derived X) (a : H ⟶ H'),
      d.completedExchange sq H ≫ (d.push f').map ((d.completedPull g').map a) =
        (d.completedPull g).map ((d.push f).map a) ≫ d.completedExchange sq H') ∧
    (∀ (H : d.derived X) (hH : PbcIsIntrinsicallyComplete X d H)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj H)),
      IsIso (d.completedExchange sq H) ∧
        d.completedExchange sq H = d.completedBaseChangeMap sq H
          (pbcIntrinsicComplete_towerComplete d X H hH) W)
```

The import interface was:

```lean
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
import Sheaf.Paper.PerfectProjectionFormula
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.CompletedReductionFiniteEvaluationNormalization
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.FourArrows
import Sheaf.Paper.FiniteReductionExchangeRectangle
import Sheaf.Paper.FiniteLevelProEtaleBaseChange
import Sheaf.Paper.StrictTowerExchangeMateNormalization
```

## New

The declaration signature is verbatim the same:

```lean
theorem completedProperIndependentOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f] :
    (∀ (H H' : d.derived X) (a : H ⟶ H'),
      d.completedExchange sq H ≫ (d.push f').map ((d.completedPull g').map a) =
        (d.completedPull g).map ((d.push f).map a) ≫ d.completedExchange sq H') ∧
    (∀ (H : d.derived X) (hH : PbcIsIntrinsicallyComplete X d H)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj H)),
      IsIso (d.completedExchange sq H) ∧
        d.completedExchange sq H = d.completedBaseChangeMap sq H
          (pbcIntrinsicComplete_towerComplete d X H hH) W)
```

Only the imports and the proof change. The imports are now:

```lean
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.Paper.PbcIntrinsicTowerComplete
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.StrictTowerExchangeMateNormalization
```

## Users

`python3 tools/downstream.py Sheaf.Paper.CompletedProperIndependentOrigins --uses
AlgebraicGeometry.Scheme.completedProperIndependentOrigins` reports no downstream
module and only the declaration's own occurrence. A source search likewise found
no current importer or caller. The parent DAG still needs this theorem; its
mathematical statement, dependency attachment and unit route remain intact.
There are no consumer adaptations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedProperIndependentOrigins | J6 | Same signature; completed proof and smaller import interface. |

## Status

landed 20261023T041442-L-1577112 2026-10-23 (merge of deliver/J6/Sheaf.Paper.CompletedProperIndependentOrigins)
