## What changed

In `Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality`, replace the
private proof import of `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison`
by the existing proved upstream module
`WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparison`. Convert the
two incoming K-flat hypotheses explicitly to the upstream predicate using the
proved private helper `canonical_kflat`, whose proof applies the hypothesis to
each acyclic test complex. Then use the same extension-comparison theorem and
the original localization/naturality argument. Its two diagram calculations
are performed by proved private `conjugate_naturality` and `paste_naturality`
lemmas over abstract morphisms, reducing expensive unfolding of the concrete
stalk terms. All three private helpers are in the same module and fully proved.

Both public imports, both declaration signatures, and the constructed comparison
map are unchanged. Update the parent node's first proof step and origin, and
reattach `lem-pc-stalk-derived-extension-comparison` to the existing upstream
declaration with its actual predicate spelling. Its mathematical statement and
proof route are unchanged. The unit route is unchanged: its `realized` lists
are empty, and all three of this item's existing mathematical dependencies are
still used. No new public theorem, definition, axiom or hole is introduced.

Change record: `coord/changes/P9-stalk-pullback-canonical-extension.md`.

## Proved and sorry left

This is a zero-hole import/dependency repair: 0 holes closed, 0 holes added,
0 split off. Both `AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback`
and `AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality`
already had complete bodies in the current shared source. Their bodies remain
complete; no declaration in this delivery contains `sorry`.

The original current file compiles without diagnostics in 19.6 seconds. The
final canonical-import version with the proved private helpers compiles
and writes its artifacts without diagnostics in 38.8 seconds. A probe importing
only the item repeats the full original theorem signature and applies it; it
compiles without diagnostics. Both public declarations print exactly `propext`,
`Classical.choice`, and `Quot.sound` as axioms: no inherited hole remains.
Delivery preflight independently checks the completed packet.

## No longer needed

Remove the direct private import
`Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison`. A recursive source
import-closure comparison shows that this also removes the following modules
from this item's import closure:

- `Sheaf.Algebra.Homology.KFlatStalkCriterion`
- `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso`
- `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso`
- `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore`

Together with the directly removed module, five Sheaf modules leave this item's
import closure. No module is withdrawn or deleted. These are local dependency
pruning figures, not a claim about the global target closure. The corresponding
mathematical nodes are still needed through the canonical upstream proof; no
mathematical proof dependency is removed. Keep the public KFlat import because
the existing public signature uses `IsAcyclicTensorKFlat`.

## Where the brief, the DAG or earlier work was wrong

The rework row still describes the pre-restoration duplicate DerivedPullback
import error. The current file already contains V4's landed restoration and a
complete proof; there is no remaining original `sorry` to close. This packet
makes a further concrete dependency repair rather than reporting that earlier
landing as new proof work.

The DAG's extension-comparison attachment still pointed to the duplicate Sheaf
module even though the same theorem is already proved upstream. Use that
canonical declaration, preserving its source-library signature. The acyclic
K-flat predicates have different names but the same defining formula; no
K-flatness assumption is weakened. Some intermediate compile runs reached the
60-second cap. Profiling checked the formula conversions and localization
bookkeeping; the final proof reuses the conversion through a private lemma
and performs conjugation and pasting over abstract morphisms in the same file.
The artifact-writing compile passes within the unchanged limit. The first
delivery attempt also reached the compile cap and pushed nothing; the packet
was retained and its diagram calculations optimized. No tool was patched or
bypassed.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
