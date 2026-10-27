## What changed

Implemented `WeilConjectures.sfFiniteOperations_restrictedAdjunction` from the
specified relative Hom chain. Private proved helpers transport intrinsic finite
homology support to bounded-below fixed-module etale origins, prove naturality
for arbitrary retained origins, and restrict a natural Hom equivalence through
fully faithful realizations. The adjunction is constructed with
`Adjunction.mkOfHomEquiv`; its normalization for every origin is proved.
Additivity, left shifts, left realization compatibility and triangulatedness
are reflected through the existing canonical realization. All existing public
signatures, definitions, instances and public imports are preserved.

One remaining part, compatibility of the right realization with the induced
adjoint shifts, is isolated in the new module
`Sheaf.CategoryTheory.SpecifiedExceptionalRealizationShift`. It assumes the
adjunction and its Hom normalization and asserts only right shift compatibility.
It neither supplies an adjunction nor asserts origins, boundedness, left
triangulatedness or preservation. The item's node records this actual route.

Both modules compile together. The new shift module took 43.6 seconds. A profiling
run of the item compiled in 33.9 seconds; its largest individual elaboration,
kernel-checking and linting costs were each about 4.6 seconds. An earlier full
check passed but took 102.4 seconds, so delivery verification must confirm the
60-second bound. Temporary profiling options and traces have been removed.
Private realization instance proofs avoid repeated unfolding in the main proof.

## Proved and sorry left

Closed the original whole-proof hole in
`WeilConjectures.sfFiniteOperations_restrictedAdjunction`
(`lem-sf-finite-restriction-normalized-adjunction`). Its proof is complete from
the imported declarations. Proved the boundedness/origin step, arbitrary-origin
left naturality, right naturality, change-of-origin normalization, the restricted
adjunction construction, additivity, triangulatedness and the left shift clause.

Added one hole:
`AlgebraicGeometry.ProEtale.specifiedExceptionalRealization_shift`
(`lem-sf-specified-exceptional-realization-shift`), the right shift clause alone.
This is a decomposition: one old hole closed, one strictly smaller hole added,
net zero holes closed. No sorry remains in the item module and no definition
contains sorry.

## No longer needed

No existing public import is removed and no entire module is withdrawn.
Both new private proof imports are used.

The proof uses the existing finite-ring essential-image criterion
`lem-weil-pbc-finite-ring-constructible-derived-origin` directly, instead of the
larger `lem-sf-proetale-constructible-origin` coefficient-encoding interface.
The latter is no longer an immediate proof dependency of this node.

`thm-amb-etale-exceptional-adjoint` remains used by the unchanged named instance
in this file, and the canonical proper/open comparison and site comparison
remain used through the specified Hom chain. The original immediate dependency
`lem-sf-class-compact-support-comparison` is now recorded under the remaining
shift step, where its shift compatibility is needed. The old direct dependency
`lem-weil-pbc-adjunction-shift-compatibility-unique` is likewise recorded under
that smaller step. The other original mathematical ingredients remain in use;
no unit route or upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original origin step was stated through a larger coefficient-encoding
comparison than necessary. The already proved finite-ring derived-origin
criterion applies directly to the intrinsic predicate of the finite-Tor object.
No mathematical statement or definition was changed. The quarantine/rework row
was read before copying the item, and its Lean attachment and dependencies are
preserved; no quarantined module is withdrawn.

## New nodes

`lem-sf-specified-exceptional-realization-shift` records only the compatibility
of the right realization with adjoint shifts, conditional on the actual
normalized relative adjunction and left realization compatibility. Its proof
plan lifts shifts through full faithfulness, checks the unit using the
specified etale Hom chain and a shifted origin, and applies uniqueness of the
compatible right shift. The node and theorem contain the source, complete proof
in words, search results and empty/zero edge-case check. No change record is
needed: existing interfaces are unchanged.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
