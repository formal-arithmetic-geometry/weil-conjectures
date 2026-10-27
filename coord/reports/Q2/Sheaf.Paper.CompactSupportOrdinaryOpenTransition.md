## What changed

The assigned ordinary-open transition is reduced by a genuine two-stage mate argument:
the direct-image section square is isolated, its first transpose gives inverse-image
compatibility, and its second transpose gives native open-extension compatibility.
Naturality of the unchanged `compactSupportOpenModel` then gives exactly the assigned
statement. No existing declaration signature or public import is changed.

The proved module `Sheaf.Paper.CompactSupportOrdinaryPullbackTransition` separates
the first transpose. The direct-image square is a remaining split obligation.
Local abstraction and separate section modules were tried, but their imported carrier
normalization exceeded the per-file compile limit.

The new module `Sheaf.Paper.CompactSupportOpenScalarRestriction` isolates the
single-level tensor-to-literal restriction coordinate square. It constructs the scalar
direct-image square and its inverse mate, proves that mate invertible, and proves the
unit equations transporting the published scalar extension-by-zero comparison.

## Proved and sorry left

The hole in `WeilConjectures.compactSupportOrdinaryOpenTransition` is closed from two
strictly smaller intermediate statements. Two holes are added:
`WeilConjectures.compactSupportOpenRestrictionModel_scalar`, node
`lem-weil-compact-support-open-restriction-scalar`, and
`WeilConjectures.compactSupportOrdinaryDirectImageTransition`, node
`lem-weil-compact-support-ordinary-direct-image-transition`. This is a decomposition,
not a net hole closure: the scalar lemma is single-level coordinate compatibility, and
the direct-image lemma is the sectionwise horizontal square.
The scalar statement involves one ring homomorphism, one open immersion, and inverse
image versus literal restriction. It contains no coefficient sequence, transition map,
open-extension functor, or evaluation comparison.

The existing proved `compactSupportOrdinaryOpenMate_isIso` and the actual definition
`compactSupportOrdinaryOpenEvaluation` are preserved.

## No longer needed

None of the original declared proof dependencies is pruned. They all participate in
the section calculation, native adjunctions, or transport of scalar normalization.
No existing module or declaration is withdrawn. No imports are removed.

## Where the brief, the DAG or earlier work was wrong

The node's proposed unit argument omits the precise scalar naturality equation for the
normalized identification of native tensor inverse image with literal open restriction.
The published normalization for `sfOpenRestriction` uses literal restriction, while
`moduleJAdj` uses native tensor inverse image. They are isomorphic but not definitionally
equal. The new node states exactly this missing coordinate compatibility; it does not
repeat the assigned system-level compatibility statement.

## New nodes

`lem-weil-compact-support-open-restriction-scalar`, in
`Sheaf.Paper.CompactSupportOpenScalarRestriction`, is the scalar compatibility of the
unit-normalized tensor-to-literal open restriction model. Its proof is by transposing
under inverse image/direct image, checking the identical section maps, and using
injectivity of the adjunction Hom equivalence. It applies to identity ring maps, the
zero ring, and the empty open; it assumes no flatness or surjectivity. The proof steps,
source, search records, and exact Lean statement are in its new DAG node. No change
record is needed because no existing interface or definition is changed.

`lem-weil-compact-support-ordinary-pullback-transition`, in
`Sheaf.Paper.CompactSupportOrdinaryPullbackTransition`, is the proved ordinary
inverse-image horizontal square. Its proof combines the sectionwise direct-image
square with the normalized evaluation-unit equations and mate calculus. It adds
no hole and involves no extension by zero.

`lem-weil-compact-support-ordinary-direct-image-transition`, in
`Sheaf.Paper.CompactSupportOrdinaryDirectImageTransition`, states the sectionwise
direct-image square used by the pullback comparison. Its proof is left as the second
split hole after attempts at direct section normalization and local abstraction.

`lem-weil-compact-support-ordinary-pullback-unit`, in
`Sheaf.Paper.CompactSupportOrdinaryPullbackUnit`, is the proved specialization of the
native evaluation-unit normalization to ordinary coefficient coordinates. It adds no
hole and separates an expensive definitional comparison from mate calculus.

The attempted auxiliary section modules were not delivered. The direct-image square
remains as a strictly smaller split obligation.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
