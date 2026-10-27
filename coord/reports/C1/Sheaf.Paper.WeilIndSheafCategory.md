## What changed

Reduce `WeilConjectures.zlPullComp_existsUnique` to naturality of explicitly
constructed common-stage components. The new module
`Sheaf.Paper.CommonStagePullbackCompNaturality` proves the literal pullback-object
formula and constructs each component by rationalizing the specified integral
compositor and conjugating by these object equalities. Its one remaining theorem
is naturality of that component family. The assigned module assembles it with
`NatIso.ofComponents`, checks the prescribed integral normalization, and proves
uniqueness by cancellation on every literal integral representative.

No existing public signature or definition body changes. The new import is private.
Normal transparency checking is enabled through the repaired theorem, with the
original settings restored before the untouched remainder, to avoid expansion
of large chosen functors. No module held by another group is adapted.

## Proved and sorry left

Closed: `WeilConjectures.zlPullComp_existsUnique` (one original hole).
Added: `WeilConjectures.commonStagePullbackCompComponent_naturality` (one hole,
node `lem-zl-common-stage-pullback-comp-naturality`). This is a decomposition,
not a net hole reduction. Naturality of one explicit family is strictly smaller
than constructing and uniquely characterizing a normalized natural isomorphism.
The component definition contains no hole and chooses no arbitrary witness.
Both modules compile with no errors. Explicit universes and the literal pair
remove repeated coefficient-model reconstruction in the component formula;
the delivery compiler now accepts the per-file runtime. Temporary profiler
settings have been removed.

## No longer needed

No existing imports removed, no existing dependencies pruned, and no modules
withdrawn. The proof avoids the earlier draft's import of
`LocalFrobeniusTrace`, extraction of `composition_scalar`, and adaptation of
`ResidueCompatiblePullbackFrobenius` (held by T1). Those undelivered drafts are
preserved in the scratchpad. The earlier proposed stage-square node and module
are also absent from this packet. The direct construction avoids copied functors
and their associated natural-isomorphism transports.

## Where the brief, the DAG or earlier work was wrong

The prior session's filesystem-full tool failure is resolved. Its preserved
private diagnostic hole and unverified descent calculation are replaced by the
public naturality obligation with a source, proof in words, and a node. The
existing `composition_scalar` predecessor lives in a module importing the item,
so importing it here would form a cycle. The component construction instead uses
the existing integral compositor and pullback-object specifications directly.
The current blueprint composition proof is under
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`.

## New nodes

`lem-zl-common-stage-pullback-comp-naturality` records naturality of the actual
normalized integral components after rationalization and inclusion into the
common-stage category. Its proof explains representative descent, the finite
coefficient scalar square, tensor naturality, and cancellation. Empty schemes,
identity stages, arbitrary scheme maps, and both coefficient universes are retained.
Change record: `coord/changes/C1-weil-ind-composition-proof.md`.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
