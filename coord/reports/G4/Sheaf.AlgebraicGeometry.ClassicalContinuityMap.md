## What changed

Proved `AlgebraicGeometry.ProEtale.affinePresentation_iff` without changing its
signature or any existing definition. The reverse implication constructs the
site presentation directly from `proAffineEtale`, enlarging its index universe.
The forward implication converts the actual affine limit cone to a global-sections
colimit, using a proved private helper and full faithfulness of Spec.

Added the proof-only import `Sheaf.RingTheory.IndEtaleSmallIndex`, its proved
ring-theoretic theorem `CommRingCat.ind_etale_small_index`, and its node.
The index-shrinking proof constructs the essentially small category of etale
R-algebras mapping to B. It has finite colimits and hence is filtered. Its colimit
C is small ind-etale, and the given larger presentation makes B a retract of C.
A proved private helper expresses this retract as the colimit of an idempotent
sequence, then applies `ObjectProperty.ind_ind` to flatten the presentations.
All choices are actual categorical colimits of constructed diagrams; no data are
chosen from an unproved existence statement. A fresh `lcompile.py --all` check on 2026-10-19 passed for both sandbox
modules without errors or warnings (the server reused its compilation cache).

## Proved and sorry left

The current repository has one original hole. Closed it in
`AlgebraicGeometry.ProEtale.affinePresentation_iff`. Proved the new theorem
`CommRingCat.ind_etale_small_index` (node `lem-pe-ind-etale-small-index`) as well.
There are zero `sorry` declarations in either delivered module, zero holes added,
and no split-offs left. The six other existing proofs in the item were already
present in the shared repository and are not claimed as progress.

## No longer needed

The new ring module imports the smaller upstream `Etale` module; it needs no
`IndEtale` import. Removed direct proof-only imports from the item:

- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`: its API is available
  through the retained module-colimit import.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`: the ring carriers are in one
  universe; only the presentation index changes universe.
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`: already available
  through the retained public comparison import.

The affine proof does not use
`lem-weil-pbc-commutative-algebras-colimits-exist`: it reflects the specified limit
through Spec to obtain the required colimit, avoiding a separately chosen ring
colimit and comparison. Removed that node from the item's proof dependencies.
The proof also no longer needs `lem-weil-pbc-spec-small-colimit-limit`: full
faithfulness of Spec reflects the given limit, and the reverse direction unfolds
the existing pro-affine presentation directly. Removed this node from the proof
dependencies as well. Other original dependencies are retained; none of their
modules is claimed globally unreachable. No blueprint unit or unit-level proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained report described one decomposition with a remaining small-index hole,
but its Lean file had subsequently replaced that hole by an invalid application of
`MorphismProperty.ind_of_univLE`. That theorem only enlarges index universes;
it cannot shrink u+1 to u. The retained explicit retract construction was repaired
and now proves the needed shrinking theorem. The original affine DAG plan also
suppressed this universe issue; the new node makes the additional argument explicit.

The construction includes zero rings and empty spectra: the category of etale
algebras over R mapping to B has the initial object R. The retract argument uses
only its stated retraction equation, including the degenerate zero-ring case.
No existing statement, definition, signature, or visibility changes.

## New nodes

`lem-pe-ind-etale-small-index`, in
`dag/nodes/sec-proetale-coefficients/lem-pe-ind-etale-small-index.json`, realizes
the fully proved `CommRingCat.ind_etale_small_index` in
`Sheaf.RingTheory.IndEtaleSmallIndex`. Its source is the original continuity-map
detail's affine universe reduction. Its docstring and node give the canonical
small-category construction and the complete retract/sequence proof.
No change records or forced adaptations are needed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
