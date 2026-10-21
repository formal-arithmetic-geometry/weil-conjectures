## What changed

Filled the three theorem proofs in
`Sheaf.CategoryTheory.EquivalenceAdjunctionComparison`, preserving all signatures,
imports, visibility, options, and docstrings.

- `exists_equivalenceAdjunctionComparison` constructs the comparison as the inverse
  of the inverse mate, using the existing equivalence theorem. Mate injectivity
  gives uniqueness; the transpose and unit/counit identities give normalization.
- `equivalenceAdjunctionComparison_compositor` follows the node's Steps 3–4:
  Mathlib's horizontal mate pasting and change-of-adjunction formulas identify
  the two mates, and cancellation gives the specified compositor equation.
- `equivalenceAdjunctionComparison_inverseMate` follows Steps 5–8: transposing
  the two routes reduces their equality to the given right square and naturality.
  It then reflects component invertibility through the fully faithful equivalence
  and transports it to all barred objects using the counit isomorphism.

The existing DAG plan and all six dependencies remain accurate. No new statements,
definitions, helpers or nodes are required. This packet changes only the three
proof bodies of the current tracked module.

## Proved and sorry left

Closed all three original holes, each attached to
`lem-sfb-equivalence-square-inverse-mate-coherence`:

- `CategoryTheory.exists_equivalenceAdjunctionComparison`
- `CategoryTheory.equivalenceAdjunctionComparison_compositor`
- `CategoryTheory.equivalenceAdjunctionComparison_inverseMate`

Holes closed: 3. Holes added: 0. Holes left: 0. Split off: 0.
The proofs use the existing proved inverse-mate and transpose dependencies and
Mathlib; this is a proof, not a decomposition.

## No longer needed

None. Both existing private proof imports are used, and the public Mathlib import
is needed by the signatures. All declared dependency nodes are used; no modules
or nodes are pruned. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect was found. The prior delivery at
`29bc2f31949` used a base predating the tracked creation of the item module and
was returned by the landing tool. For this repair, the current shared source was
read in full and all three completed proof bodies were applied to that source.
A mechanical comparison confirmed that every character outside the proof bodies
is identical to the current source: no signature, import, option, visibility or
docstring changed. The obsolete restoration change record from the prior packet
was removed; the module already exists in the current tracked library. The DAG
plan is unchanged and continues to match all three proofs.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
