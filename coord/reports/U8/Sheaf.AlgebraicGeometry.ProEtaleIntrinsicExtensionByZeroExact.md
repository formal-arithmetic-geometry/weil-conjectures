## What changed

Proved `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_exact` without changing any
statement, definition, universe, or declaration visibility. The defining functor already
uses `ProEtale.openImmersionLowerShriek`, whose additive and finite-limit-preserving
instances exist in the source library. Its adjunction supplies finite-colimit preservation.
The two canonical coefficient equivalences preserve limits and colimits; their forward
functors are additive by `finiteCoefficientIntrinsicRealization_additive`, and Mathlib
`Equivalence.inverse_additive` supplies additivity of their inverses. Composition completes
the proof. Updated the theorem docstring and its existing node to record this actual route.

The shorter route uses the already closed node `lem-sfb-finite-extension-by-zero-exact`
as a generic tool for the precise middle functor in the definition, rather than rebuilding
that exactness result by comparison with another extension construction. The item's unit
`dag/units/sk-def-sf-operations.json` has no realized statement or steps to bypass.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_exact`
(node `lem-weil-extension-by-zero-exact`). Proved 1 of 1 original sorries; added 0 holes;
split off 0 theorems. There are no sorries left in the delivered module.
The three existing public instances now use this complete proof.

The proof still uses the existing canonical realization theorem
`AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_exact`
from `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`; its existing hole
is outside this delivery and is neither duplicated nor moved. Thus this delivery closes
one local hole and does not claim the full transitive axiom closure is already sorry-free.
The proof applies uniformly to the identity open immersion, empty opens, and the zero
coefficient ring, without any new nonemptiness or nontriviality assumption.

Validation: the original proof and the pruned-import version compiled successfully through
`lcompile.py`. The first dry run required a change record for removal of a redundant public
import, so the original public header was restored; no public import is changed. The
required final delivery dry run checks the final module and unchanged signatures.

## No longer needed

Removed these seven unused proof-only imports:

- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.Algebra.Category.Ring.Limits`.
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.

The two original public imports are retained as the existing public interface.

The proof no longer needs nodes `def-weil-extension-by-zero-presheaf`,
`lem-pur-site-restriction-module-adjunction-exact`, or
`lem-weil-proetale-weakly-etale-localization`: the middle functor is already the source
library's exact lower shriek, so no explicit localization or direct-sum comparison is needed.
Their defining modules are unnecessary for this proof; this makes no claim that other
parents in the whole project no longer use them. The existing intrinsic-extension
module remains required, and its coefficient-realization dependency is used directly.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was mathematically valid but longer than necessary for the actual
Lean definition. It proposed constructing a localization-and-presheaf comparison even
though the canonical fixed-coefficient lower shriek in the definition already has exactly
the additive and finite-limit-preserving instances required here, together with its left
adjoint structure. No statement was found false or changed. No new nodes, definition
repairs, change records, or forced consumer adaptations are needed.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
