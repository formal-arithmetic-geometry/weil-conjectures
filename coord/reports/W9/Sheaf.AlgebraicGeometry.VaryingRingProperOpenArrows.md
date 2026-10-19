## What changed

The module compiles cleanly through `lcompile.py` in 5.1 seconds. The earlier compile
service outage has cleared. The unavailable compiled `PlusCompatNat` import was
replaced by the built `PlusCompatibility` interface; the homology comparison is now
a composite of existing natural isomorphisms, with no separate naturality proof.

Proved the three remaining invertibility clauses in
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`, preserving all existing signatures,
public imports, definitions and docstrings. Private categorical helpers transport the
existing arbitrary-ring strict-tower results through constant embedding and evaluation,
use the specified evaluation mates and joint detection of isomorphisms, and recover
ordinary module statements by degree-zero single-complex homology. No equality of
arbitrary derived maps is inferred from evaluation.

The cartesian comparison is proved by showing that its target belongs to the essential
image of open extension. Its prescribed transpose and the open counit are both invertible.
For the clopen comparison an ordinary extension/direct-image isomorphism transfers full
faithfulness; the specified comparison then consists of two invertible factors.

Added proof-only imports for adjunction full faithfulness, Grothendieck-category enough
injectives and the existing bounded-below compatibility for degree-zero derived direct image.
Updated the existing DAG node's proof and proof dependencies to describe these arguments.

## Proved and sorry left

Closed all three original holes (all under `def-sp-varying-ring-proper-open-arrows`):

- `AlgebraicGeometry.ProEtale.VaryingRing.moduleBetaInv_isIso`.
- `AlgebraicGeometry.ProEtale.VaryingRing.moduleJAdj_unit_isIso`.
- `AlgebraicGeometry.ProEtale.VaryingRing.moduleOpenToP_isIso`.

No `sorry` remains in this module; no hole or split theorem is added elsewhere.
The proofs use existing stated dependencies, including the arbitrary-ring strict-tower
base-change and clopen invertibility clauses, and semilinear derived-section detection.
These dependencies retain their own proof obligations.

## No longer needed

No repository import or existing proof dependency was removed, and no existing DAG node
or module is pruned. The earlier temporary direct ringed-site proof and its three
proof-only imports (`ProEtaleRingedOpenClosed`, `ProEtaleOperations`, and
`ProEtaleRingedOpenComparison`) were removed from the working draft: the existing
strict-tower unit theorem supplies that argument. No new coherence lemma for evaluated
square compositors is needed; essential-image membership suffices for invertibility.

## Where the brief, the DAG or earlier work was wrong

The existing DAG proof listed only the previously completed naturality and equality
transport clauses and explicitly left the three invertibility clauses open. The added
steps now describe their complete Lean proofs from the existing declared interfaces.
There is no statement correction or definition repair, no consumer adaptation, and no
change to the unit route. Constant-ring strict-tower results and semilinear detection
serve as tools for the same varying-ring construction.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
