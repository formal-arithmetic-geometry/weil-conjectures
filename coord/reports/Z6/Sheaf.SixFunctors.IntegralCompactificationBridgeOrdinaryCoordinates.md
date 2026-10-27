## What changed

Replaced the proof hole in
`WeilConjectures.IntegralCompactificationBridge.ordinaryDirectModel_existsUnique`
by a construction from the existing `constantDirectUnderlying` isomorphism and one
new local scalar-action equation. The original theorem signature, chosen definition,
tower transports and public imports remain unchanged.

The inverse underlying comparison is additive by naturality on biproduct inclusions,
projections and their sum. The scalar-action equation then makes each section map
linear. Underlying naturality proves the module-presheaf and module-functor naturality.
The two inverse identities prove sectionwise bijectivity, hence invertibility. Finally,
the section normalization and the underlying inverse identities force equality of
all section maps and therefore uniqueness of the natural isomorphism.

The parent DAG proof now records precisely this argument. The scalar equation lives
in its own module with its source and proof in words. No consumer adaptation or
definition/statement change is required.

Profiler validation found approximately 0.6 seconds of elaboration in the new
scalar module and roughly 5 seconds in the assigned proof; the profiling run
reported total file times of 37.1 and 40.2 seconds. Profiling options were removed
for the final compile and delivery. The final assigned-module compile passed
without warnings in 9.9 seconds; the unchanged scalar module previously passed
without warnings in 53.6 seconds.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralCompactificationBridge.ordinaryDirectModel_existsUnique`
(node `def-sf-integral-compactification-ordinary-site-transport`). Its combining proof
has no `sorry`. The private helper `underlying_add` is proved.

Added one hole:
`WeilConjectures.IntegralCompactificationBridge.ordinaryDirectUnderlying_smul`
(node `lem-sf-integral-compactification-ordinary-scalar-action`, module
`Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction`). Its proof is
exactly `by sorry`. This is only compatibility with one local scalar operation on
an already specified underlying comparison. It supplies no module comparison,
additivity, naturality, invertibility or uniqueness. The docstring proves it in words
using the normalized Hom bijection and the constant sheafification unit.

This is a decomposition: 1 original hole replaced by 1 strictly smaller hole,
net hole decrease 0. The item module itself has 0 holes.

## No longer needed

Removed the unused private proof imports
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` and
`Sheaf.SixFunctors.AmbientProperOpenPasting`. The proof uses neither the tower-limit
comparison nor ambient proper/open pasting. No DAG proof dependency was formerly
listed, so no existing dependency node is withdrawn. Both imported modules remain
available to their other consumers; this delivery claims no whole-module pruning.

The existing public re-exports are preserved as part of the consumer interface.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned module has one hole, but its definition node had an empty `proof` and
`proof_deps`: there was no numbered plan to translate. The docstring supplies the
actual sectionwise route. A local scalar equation was missing from the existing
API; the already stated isomorphism compares underlying sheaves of sets, which
does not by itself supply linearity over arbitrary local ring sections.

## New nodes

`lem-sf-integral-compactification-ordinary-scalar-action` states that the inverse
of `constantDirectUnderlying`, evaluated on `sfCbcModelModules V M`, commutes with
every scalar section of the small-model constant coefficient ring. This is the
scalar-action step of the parent's source, Stacks Project `sites-modules.tex`,
Tags 03D2 and 03D7. The statement includes all module sheaves and schemes, including
zero modules and empty schemes, and adds no finiteness or inhabitedness condition.
Searches with LeanSearch, LeanFinder, Loogle and source grep found only generic
pushforward and adjunction comparisons, not this specialized normalization equation.
The new module is imported privately by the assigned module; it does not import
its parent and creates no cycle. No change record is needed because existing
signatures, data, visibility and public imports are unchanged.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
