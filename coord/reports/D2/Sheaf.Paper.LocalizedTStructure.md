## What changed

Completed `AlgebraicGeometry.Scheme.pbc_localized_tstructure` in
`Sheaf.Paper.LocalizedTStructure`, preserving its statement and all existing definitions.
The rational bounds are the essential images of the integral bounds. Shift compatibility
and mapped integral truncation triangles give the shift and existence axioms; tensor
induction on the integral Hom module proves orthogonality. Integral bounds give boundedness.
The existing t-exact-functor comparison API gives both natural truncation isomorphisms.
Applying those comparisons to integral H⁰ proves the single-object heart description.
The integral truncation theorem supplies the conditional derived-limit computation,
with the upper truncation reindexed from m-1 to m.

Retained the earlier attempt's completed outer argument and repaired its t-exactness
instance syntax. Proved its unfinished core directly and integrated it into the assigned
module. The temporary, previously unsubmitted `LocalizedTStructureCore` module is removed
from the sandbox; it never entered the library. Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.pbc_localized_tstructure` (one original hole).
Added: zero holes. Remaining in the delivered module: zero.
This is a proof from existing declared dependencies, not a decomposition. Its existing
integral-category and integral-truncation dependencies retain their own proof obligations.
Validation: the complete module compiles through `lcompile.py`; delivery preflight also
checks signatures, axioms and the hole ledger.

## No longer needed

Removed redundant proof-only imports `Sheaf.Paper.IntegralCanonicalTruncations`,
`Sheaf.Paper.IntegralUniformCoefficient` and `Sheaf.Paper.PbcRationalCategory`:
the needed declarations are already publicly available through `IntegralTStructure`.
The first and third nodes still describe notions used by the proof; they are not pruned.
`IntegralUniformCoefficient` is not used directly here; it remains an integral-truncation
dependency, so this delivery does not claim to prune it from the targets' closure.

All declared proof-dependency nodes are retained: in particular,
`lem-weil-heart-short-exact-triangles` is realized by the source Homology module,
whose `homology₀` construction the heart argument uses. Its additional short-exact-sequence
and long-exact-sequence clauses are not invoked. No new nodes or whole modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox was incomplete: no report or node update, one unfinished core theorem,
and an invalid `have ... where` t-exactness instance. These are repaired. The source
statement and its explicit Tor condition are unchanged. Tensor-Hom orthogonality requires
unfolding the localization category and functor locally before tensor induction; no
library definitions needed repair. The unit `sk-rem-rest` has no realized statement or
proof-step constraint to bypass. The current blueprint's scalar-localization route is
retained; the previously reviewed conditional tower clause is preserved verbatim.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
