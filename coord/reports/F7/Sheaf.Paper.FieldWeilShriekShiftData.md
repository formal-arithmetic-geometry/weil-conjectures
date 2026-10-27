## What changed

Filled the five remaining proof holes in `Sheaf.Paper.FieldWeilShriekShiftData`.
The integral comparison is obtained from the stated coherent integral shift system;
signed cocone coordinates and good-localization descent prove its uniqueness.
The rational and common-stage comparisons are normalized against this fixed shift.
A private elementary lemma shows that a coherent integer-shift structure is
uniquely determined by its comparison at one.

For finite operations, restrict the completed integral adjunctions to the full
constructible subcategories and tensor their units and counits to rational Homs.
Uniqueness of adjoints identifies the chosen proper/open functors with the recorded
finite-support functors. Their composition and equality transport give the
comparison for arbitrary compactifications. This uses finite type and
quasi-compactness over the coefficient field, without separated structure maps.

Added private proof imports for the coherent shift systems, signed cocone
extensionality, localization, integral/rational adjunctions, open-factor coherence,
open identity normalization, compact-support composition and geometric
compactification identities. Updated the existing node's proof and proof dependencies
to follow these arguments. Existing public signatures, definitions, public imports,
and the two proofs previously supplied by J3 are preserved. Local instance and
transparency settings prevent overlapping completed-module instances and unnecessary
unfolding while checking normalized shifts. Explicit functor expressions avoid repeated
unfolding of local aliases in the adjunction proofs. The open comparison passes its
local isomorphism proof explicitly rather than repeating instance search. The full
module compiled without warnings in 43.9 seconds. Excluding the additional overlapping
monoidal/sheafification instances already excluded in the imported proofs reduced
the complete diagnostic compile to 38.5 seconds without warnings.

## Proved and sorry left

Five existing holes closed, all in node
`def-zl-field-weil-shriek-shift-data`:

- `WeilConjectures.fieldIntegralPullShift_existsUnique`.
- `WeilConjectures.fieldRationalPullShift_existsUnique`.
- `WeilConjectures.fieldCommonPullShift_existsUnique`.
- `WeilConjectures.fieldWeilPull_adjoints`.
- `WeilConjectures.fieldWeilShriek_recorded`.

No `sorry` remains in the item module. No holes or public statements were added;
no results were split off. These are proofs from the project's stated dependencies,
including their existing unfinished theorems, rather than claims that the entire
transitive dependency closure is axiom-free.

## No longer needed

No existing imports, nodes or modules are withdrawn. The original composition and
semilinear dependencies remain necessary for the earlier J3 proofs. The new proof
uses the already stated general shift and adjunction interfaces, avoiding any new
intermediate theory or split nodes.

## Where the brief, the DAG or earlier work was wrong

The existing DAG proof described only the two holes J3 had already closed; it did
not describe the remaining normalized shifts, adjoints, or recorded-support
comparison. The updated steps cover them without changing the node's statement.
The integral existence theorem has no residue-field inversion hypotheses, so the
unconditionally quantified integral part of the coherent shift system is accessed
through the empty scheme, whose inversion condition is vacuous. No additional
hypothesis is imposed on the given source or target scheme.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
