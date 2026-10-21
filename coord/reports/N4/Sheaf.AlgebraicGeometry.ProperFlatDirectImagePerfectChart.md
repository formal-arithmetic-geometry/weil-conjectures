## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart`
from the path recorded in `coord/rework.tsv`. Replaced its public import of the withdrawn,
empty `Sheaf.AlgebraicGeometry.DerivedPullback` with the adopted declaration owner,
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. The entire theorem signature and
complete archived proof remain verbatim. Restored its sole archived caller,
`Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart`, with exactly the same one-line
public-import correction; all of that module's statements and proofs remain verbatim.
Updated the node proof description to name the specification theorem the Lean actually uses. The Lean attachment and all dependencies stay.

## Proved and sorry left

The restored `AlgebraicGeometry.Scheme.exists_properFlatDirectImagePerfectChart` has a
complete proof. The archived item had zero holes: zero holes closed, zero added, zero left;
zero split off. The restored caller's `AlgebraicGeometry.Scheme.exists_picardSingleRankPerfectChart`
and its two private helpers also have zero holes; no hole is closed or added there.
This is a compilation restoration, not a new mathematical proof or decomposition.
Single-file server compilation passed cleanly in 13.1 seconds after the import correction.
The proof uses the existing affine Cech model, relative-flatness lemma, bounded-flat K-flat
criterion, tensor-single comparison, and derived-pullback specification. It keeps independent
universes u and w and all original hypotheses and conclusions.

## No longer needed

Removed only the import of the empty, withdrawn module
`Sheaf.AlgebraicGeometry.DerivedPullback`; its adopted source module supplies the same
recorded API. No mathematical dependency, node, or occupied source declaration is pruned.
No new nodes, modules or theorems are introduced. Search via LeanFinder found ordinary
flatness declarations; Loogle found the strict complex bounds used by the existing proof;
launcher grep found no shorter proper-flat-perfect chart result. The existing proof is retained.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantined build repair, not an unproved theorem. Its archived import
no longer supplies `derivedPullback` or `derivedPullback_spec`: compiling it unchanged reports
unknown identifiers at lines 80 and 119. The adopted source module supplies both and its
specification fits the archived proof without changes. The old node text incorrectly said to
unpack `exists_derivedPullback`, whereas Lean uses `derivedPullback_spec`; corrected that text.

The sole direct caller is the quarantined `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart`.
Its call at line 155 consumes the identical existential tuple. Counterfactual compilation of
its unmodified archive against the restored item reports at line 151 that `derivedPullback`
is imported privately and needs a public import of its adopted source owner. Its secondary
rank-instance error follows that invalid public signature. Applied exactly the same one-line
import correction to this unclaimed caller; no statement or proof changes. Both modules
were read from their rework.tsv archives. The caller's Lean attachment and dependencies stay.

The caller's sole direct user, the archived `PicardUniversalSingleRankLocus`, uses its
unchanged `exists_picardSingleRankPerfectChart` tuple at line 86, with no direct occurrence
of `derivedPullback`. No adaptation is needed there. The restored caller compiled cleanly
against the item's sandbox artifact in 14.4 seconds. No live consumer is changed.
DAG parents and the cube unit route are preserved. The generic downstream tool does not index
the absent quarantined item, so direct search of both lean/ and quarantine/ checked consumers.

Change record: `coord/changes/N4-ProperFlatDirectImagePerfectChart-restoration.md`.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
