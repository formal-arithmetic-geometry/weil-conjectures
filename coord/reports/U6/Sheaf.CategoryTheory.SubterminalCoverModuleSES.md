## What changed

Added proof-only imports of `Sheaf.CategoryTheory.SubterminalModuleLocalCalculus`
and the Mathlib additive-functor biproduct API.
The proof of `SheafOfModules.SubterminalCover.shortExact` uses its intersection
comparisons and counit equations. Private helpers prove naturality by the
adjunction Hom equivalence, the two elementary matrix splittings, and joint
detection of short exactness (including mono and epi). The complex clauses are
applications of module naturality and short exactness in each degree.
All existing signatures, definitions and public imports are preserved.
The instance-removal commands are scoped separately to the proved declarations;
see `coord/changes/U6-subterminal-cover-proof-elaboration.md`.

## Proved and sorry left

Closed the original hole `SheafOfModules.SubterminalCover.shortExact`
(`lem-sp-subterminal-cover-module-ses`): 1 of 1 original holes closed.
No holes remain in the delivered module. Zero holes added; zero split off.
The complete module compiled through `lcompile.py` (exit code 0).
The imported `SubterminalLocal.subterminal_module_local_calculus` is the existing
stated proof dependency, not a declaration introduced by this packet.

## No longer needed

None. The proof follows the existing node route. Every existing public import is
retained. The proof imports supply the stated local-calculus dependency and
biproduct preservation by additive functors.
The source and Mathlib searches found the general short-complex splitting API,
which is used for the two local matrix calculations. The Mayer-Vietoris API for
free abelian representables does not supply the arbitrary module-sheaf sequence.

## Where the brief, the DAG or earlier work was wrong

None. The existing local-calculus declaration supplies all the comparison and
compatibility data needed by the planned local split calculation.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
