# AlgebraicGeometry.Scheme.proEtaleFiniteCDProperOpenInterchange

## Reason

The proof uses the already proved source-library finite-CD comparison theorem directly,
so its former public import of the Sheaf existential packaging is unnecessary.
The theorem statement and every definition are unchanged. Three direct proof imports
are redundant through the public imports of ProperExceptionalOpenBaseChange.
The private scoped `open SheafOfModules in` only shortens the name of the universe-explicit
Grothendieck theorem in this proof; it does not change the elaborated theorem signature.

## Old

```lean
public import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison
```

## New

The four lines above are removed. The new proof-only imports are:

```lean
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import Mathlib.CategoryTheory.Monad.Adjunction
```

No declaration signature, universe, visibility, or definition body changes.
In particular every target statement has exactly the same meaning.

## Users

`python3 tools/downstream.py Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange`
reported zero downstream modules on 2026-10-19. The assigned item is available for a
parent's future proof, as the dispatcher brief permits. A library-wide textual search
finds no use of `exists_rightDerived_computes_acyclic_of_finite_dimension`, the only
declaration of the removed public Sheaf module, outside its own definition. The
remaining removed imports are already exported by the retained dependency
ProperExceptionalOpenBaseChange. No consumer adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | K6 | Same theorem signature; proof completed; redundant exports pruned. |

There are no downstream consumers to list or adapt.

## Status

landed 20261019T154015-L-3027082 2026-10-19 (merge of deliver/K6/Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange)
