## What changed

Retired the listed duplicate Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural
using deleted.txt. The existing upstream theorem of the same name proves the same
conclusion with fewer assumptions. Redirected the only direct importer,
Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow, to upstream and removed
hC from the upstream application. A lambda specializes the stronger result to
the retained flatness hypothesis. Kept the consumer's full public signature. Reattached the existing DAG node to upstream;
its statement, proof steps, proof dependencies and unit route remain valid.

Change record: coord/changes/B9-retire-kflat-localized-tensor-comparison-natural.md.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero holes left in the
retired item or the adapted consumer. This is the listed duplicate retirement,
not a decomposition or a claim of a newly proved theorem.
ModuleCat.exists_kFlatLocalizedTensorComparison_natural remains available from
WeilConjectures.Algebra.Homology.KFlatLocalizedTensorComparisonNatural, with its
complete existing proof. ModuleCat.exists_localizedTensorComparison_derived_arrow
keeps its complete proof and exact statement.

## No longer needed

The duplicate Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural module
and its import from Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow
are removed. Its private coefficient-map and K-flatness helper copies disappear
with the duplicate; upstream retains its original complete proofs unchanged.
No mathematical node is pruned: lem-pc-kflat-localized-tensor-comparison-natural
now attaches to upstream, so unfinished DAG parents retain their stated dependency.
No other import or dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The generic prove brief describes an unfinished obligation split seven times.
The current source already contains a complete proof and coord/retire-items.tsv
explicitly lists this module for retirement. The upstream version differs only
by dropping unused flatness and A-derived-category assumptions, so the retirement
must migrate the consumer's argument list as well as its import. No mathematical
claim is disputed and no source-library declaration is removed or modified.

## Forced adaptations

The retired module is imported only by
Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow (unclaimed in the
shared snapshot). Its import must change to upstream in this same packet. The
upstream theorem omits hC, so the original application passing hC in the hQ slot
would have the wrong argument type. Replace that application with upstream's hQ
application, specialized by a lambda to the retained flatness hypothesis. These
are the only changes to this consumer: import line 11 and application lines
129-130. No existing signature, visibility, docstring or other proof step changes.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
