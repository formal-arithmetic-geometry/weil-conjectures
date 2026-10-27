# AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange

## Reason

The existing canonical projective-line exchange proves the assigned affine-line case by
restriction to the standard affine chart. Three unused public imports in two unclaimed
Sheaf modules prevented this reuse: they reached CompactModelAffineLineExchange through
Stability, Finiteness.Deligne, SmoothGenericDirectImage and SmoothCompactDualModel.

Replace these imports with the lower-level exceptional-map API actually used by the
modules. This removes the cycle without duplicating the projective-line proof, choosing
any data, or splitting off another instance of the affine-line obligation. Neither shared
module changes any declaration, signature, definition body, proof body, attribute or option.
No adopted source-library signature, public import or non-theorem body changes. No target
statement or definition changes meaning.

## Old

ProjectiveLineTraceModel imports:

```lean
public import Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineKunneth
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
```

ProjectiveLineExceptionalBaseChange imports:

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.ProjectiveLineBaseChange
import Sheaf.SixFunctors.ProjectiveLinePresentations
import Sheaf.SixFunctors.ProjectiveLineTraceAdjunction
import Sheaf.SixFunctors.ProjectiveLineTraceCounitBaseChange
```

## New

ProjectiveLineTraceModel imports:

```lean
public import Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
```

ProjectiveLineExceptionalBaseChange imports:

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.CategoryTheory.Adjunction.MatesCounit
import Sheaf.SixFunctors.ProjectiveLinePresentations
import Sheaf.SixFunctors.ProjectiveLineTraceAdjunction
import Sheaf.SixFunctors.ProjectiveLineTraceCounitBaseChange
```

## Users

Both changed shared modules were unclaimed when inspected. The following are all their
live direct importers, independently confirmed with tools/downstream.py --direct. Copies
are compiled against the replacements in the sandbox, then removed without delivery.
The assigned item also compiles against the replacements. The clean counit-base-change
consumer check completed in 21.6 seconds; the assigned item in 48.7 seconds and the
SmoothBaseChange consumer in 46.5 seconds. There are no consumer edits
or forced adaptations. Existing node attachments and dependencies of the shared modules
remain correct: their constructions and proofs are byte-for-byte unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange | C3 | Same trace constructions; unchanged consumer checked. |
| Sheaf.SixFunctors.ProjectiveLineTraceAdjunction | D3 | Same counit and diagonal data; unchanged consumer checked. |
| Sheaf.SixFunctors.ProjectiveLineTraceCounitBaseChange | unclaimed | Same trace, counit and comparison; unchanged consumer checked. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange | unclaimed | Same canonical projective-line theorem; unchanged consumer checked. |
| Sheaf.AlgebraicGeometry.CompactModelAffineLineExchange | R4, assigned item | Now reuses canonical projective-line exchange through its standard open chart. |

## Status

landed 20261026T135749-L-4062135 2026-10-26 (merge of deliver/R4/Sheaf.AlgebraicGeometry.CompactModelAffineLineExchange)
