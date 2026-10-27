## What changed

Completed the main theorem from two strictly partial statements and proved private helpers.
The existing declarations and their signatures, all definitions, and all public imports
are unchanged. The proof shows sigma invertibility using ordinary etale smooth duality,
reflects the existing smooth Cartesian tower equation through faithful comparison pullback,
derives source base change by normalized eta transport and cancellation, and proves
finite-expression locality by structural induction, including inverse, tensor, and pullback.
The two new modules state the remaining smooth-triple cocycle/source-etale argument and
the three primitive open-restriction squares, with explicit maps, sources, and proof docstrings.

## Proved and sorry left

The original theorem
`AlgebraicGeometry.ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality`
(node `lem-pur-dualizing-sigma-cocycle-locality`) is assembled without sorry from the
new intermediate statements and the existing declared geometric dependencies.
Holes closed: one. Holes added: two, by declaration:

- `AlgebraicGeometry.ProEtale.DualizingLocality.dualizing_cocycle_source_etale`
  (`lem-pur-dualizing-cocycle-source-etale`).
- `AlgebraicGeometry.ProEtale.DualizingLocality.dualizing_primitive_open_restriction`
  (`lem-pur-dualizing-primitive-open-restriction`).

This is a decomposition, not a net proof gain. No sorry remains in the item module;
none is added inside a definition or a private helper. All three modules compiled through
`lcompile.py`; the final item check completed cleanly with exit code 0 (53.2 seconds),
with no warnings after removing the temporary profiler setting.

## No longer needed

The proof-only imports `Sheaf.Paper.CompositionTensorMate`,
`Sheaf.Paper.FiniteSiteCounitProjectionTransport`,
`Sheaf.Paper.CanonicalOriginCompactSupportComposition`, and
`Mathlib.CategoryTheory.Adjunction.Mates` from the earlier sandbox were not needed by
the assembly and base-change/induction proofs. The first three geometric ingredients
remain needed in the proof plan of the cocycle intermediate; no global withdrawal or
pruning of their modules is claimed. The original public imports are retained.
The parent now uses the existing source theorem recorded by
`lem-sf-smooth-dualizing-complex-invertible` for the same orientation-free smooth tensor
input, and `lem-weil-pbc-fixed-module-derived-hom-bijection` as a generic faithfulness
tool. These are not changes to the unit route: their uses are invertibility of the
canonical theta and reflection of a morphism equality, respectively.
The parent no longer directly invokes `thm-sf-comp-composition` or
`lem-weil-pbc-mate-pasting`; those are localized in the cocycle intermediate.
Its obsolete top-level tool-use approvals for these two nodes are removed, with
its tensor/pullback tool-use entries retained in order. The new cocycle node declares
the two moved generic tool uses for independent review in its split report.

## Where the brief, the DAG or earlier work was wrong

The earlier server device-full error has cleared: remote Lean now runs. Its first
check exposed an incorrectly oriented whisker-exchange rewrite, missing smoothness
and compactification instances, and expensive unification of concrete derived tensor
structures. Proof elaboration now caches the existing tensor instances with local
irreducibility, following the dependency module's established approach. No definition,
compile limit, launcher script, or target statement is changed. The previous partial
private helpers were not proofs of the main conjunction. The remaining intermediate
statements are strictly subsets: neither includes sigma invertibility, source/Cartesian
base change, or finite-expression locality.

The dependency audit also found a pre-existing mixed statement/proof cycle outside this
item: `lem-pc-ring-hom-extension-differential` has proof dependency
`lem-pc-ring-hom-extension-differential-adjacent`, whose statement depends on the former.
These shared nodes are unchanged. No dependency path returns to any of this delivery's
three edited/new nodes. Their proof-dependency lists equal the unions of their proof uses.

## New nodes

`lem-pur-dualizing-cocycle-source-etale`, in
`Sheaf.Paper.DualizingCocycleSourceEtale`, records old proof Steps 1--3: associate the
specified exceptional compositors, apply the tensor-mate identity at omega_h, cancel,
and derive normalized etale source compatibility. Edge cases: identities, empty
schemes, and dimension zero use the same isomorphism cancellations.

`lem-pur-dualizing-primitive-open-restriction`, in
`Sheaf.Paper.DualizingPrimitiveOpenRestriction`, records old Step 6 using Steps 1--5:
factor a compatible open restriction into Cartesian target restriction and source-open
inclusion; use the normalized rho/c/eta comparisons and Cartesian exchange pasting.
The front/back squares in its beta clause are Cartesian; arbitrary open faces are not.
Neither statement quantifies over arbitrary commuting morphisms or assumes its own
conclusion. Searches found no Mathlib or source-library theorem of these exact parts.
Change record: `coord/changes/D4-dualizing-local-proof-elaboration.md` records the
private import changes and file-local proof elaboration settings. Existing public
interfaces and definitions are unchanged; no consumer adaptation is forced.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
