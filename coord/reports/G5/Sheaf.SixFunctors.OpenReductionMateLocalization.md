## What changed

The item constructs its source comparison as the prescribed shriek of the reduction model
followed by exact-open localization, and constructs its target comparison from exact
completed-ring open localization and the reduction model on the extended complex.

The proof compares the two arrows using the system-open adjunction Hom equivalence. Private
proved helpers compute the localized unit and Hom equivalence from the original exact
adjunction. The ordinary transpose calculation is degreewise `unit_mateEquiv_symm`.
The derived calculation uses that same identity, naturality of `reductionPull`,
`realization.model` on the extended representative, and naturality of the reduction model
on the ordinary open unit. Both arrows are whole-system arrows throughout.

One new proof-only import, `Sheaf.SixFunctors.OpenExtensionGoodComplex`, isolates the purely
geometric preservation of good representatives. The item's public import and theorem
signature are unchanged. No existing module besides the item is modified.

Validation: `lcompile.py --all` compiled both sandbox modules without errors or
warnings and passed the compile service's per-file runtime acceptance check.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.IntegralSystemRealization.openReduction_mate_localization` (one of one).

Added one hole:
`WeilConjectures.IntegralSystemRealization.openExtension_goodComplex`
(node `lem-sf-open-extension-good-complex`). It asserts only that actual completed-ring
open extension, and its subsequent ordinary restriction, preserve flat-term K-flat
complexes. It has no realization, coefficient-reduction comparison, mate, existential
comparison isomorphism, or arrow-normalization conclusion. Its docstring gives the
slice-extension and ringed-topos-pullback argument, and its node names the existing
slice and K-flat declarations needed for the transport.

This is a decomposition, with net zero holes closed. No `sorry` remains in the item;
one remains in the new module. There are no hollow definitions or axioms added.

## No longer needed

No imports or modules are withdrawn. No unit-level route is changed. The proof uses
the definitions from `OrdinaryOpenReductionMate`, but does not need its separate
`ordinaryOpenReduction_isIso` theorem. The direct proof dependency
`def-a1-flat-term-kflat-complex` remains a statement dependency and is used by the new
preservation node; it is not withdrawn. The geometric preservation argument is delegated to
the new node rather than hidden in the mate-normalization proof.

## Where the brief, the DAG or earlier work was wrong

The original plan's assertion that the extended representative is good needs a bridge
from the existing literal ringed-slice flat-resolution theorem to the actual
completed-ring open-extension functor. `proEtaleOpen_slicePresentation` supplies an
ordinary equivalence and adjoint-uniqueness isomorphism; it does not expose the
flatness and total-tensor transport as an API theorem for this actual functor. This
geometric transport is the remaining obligation. The harder comparison of the
specified derived and ordinary mates has been written out, without another split of
the localization assertion itself. No statement was found false or weakened.

## New nodes

`lem-sf-open-extension-good-complex`, in
`dag/nodes/sec-six-functors/lem-sf-open-extension-good-complex.json`, realizes the
geometric first step of the item. Its two conclusions are good extension and good
restriction of that extension. The argument uses the existing slice presentation,
flat-resolution preservation, and ringed-topos K-flat pullback nodes. Empty and
identity opens, zero complexes, and unbounded complexes satisfy the same argument;
there are no quasi-compactness or coefficient invertibility assumptions.

The item node's proof and proof dependencies now describe the explicit comparisons
and the proved adjunction calculation. No change record is needed: existing public
interfaces are unchanged.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
