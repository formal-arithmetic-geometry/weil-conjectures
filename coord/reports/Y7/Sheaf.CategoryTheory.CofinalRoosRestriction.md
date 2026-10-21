## What changed

Implemented `CategoryTheory.CofinalRoos.cofinalRoosRestriction` in
`Sheaf.CategoryTheory.CofinalRoosRestriction`, following the node's explicit
finite-block homotopy argument. The original public statements and constructions
are unchanged. All additional constructions and lemmas are private proof helpers.
The countable-products witness for complexes is registered only locally.
Preflight requested the change record
`coord/changes/cofinal-roos-proof-support.md` for the new proof sections and commands.

For an arbitrary increasing subsequence, finite sums telescope to the required
square. The least selected index above each index defines the extension map;
extension by zero defines the other inverse coordinate. Finite prefix sums give
the contraction identities. Mathlib's mapping-cone homotopy constructor then
supplies a homotopy equivalence before shifting, and hence the required
quasi-isomorphism after shifting. Product projection calculations prove
naturality, composition, identity and the augmentation equation for the same
explicit cone map.

Searches through `msearch.py` (LeanFinder, Loogle and grep), the source library,
and `lean/Sheaf` found mapping-cone and homotopy infrastructure and the existing
arithmetic-subsequence special case. None replaces the arbitrary-subsequence
comparison. No arithmetic, resolution or derived-limit comparison is imported.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.CofinalRoos.cofinalRoosRestriction`
(node `lem-fix-cofinal-roos-restriction`). One hole closed; zero holes added;
zero holes left. No split-off statements.

Validation: `lcompile.py` compiled the complete module successfully (13.0 seconds).
The public constructions and theorem signature were compared with the source
and are unchanged; the module contains no `sorry`.

## No longer needed

Removed the redundant private import `Mathlib.Algebra.Homology.Homotopy`;
`StrictRoosModel` already supplies the homotopy API.

No mathematical dependency or module is pruned: the proof implements the existing
nine-step plan. All stated proof dependencies are definitions or Mathlib's
homotopy invariance machinery, used by the explicit construction and
`HomotopyEquiv.quasiIso_hom`. The exact-countable-products hypothesis is retained
as stated; the explicit homotopy equivalence itself needs only countable products.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The homotopy is constructed on the
unshifted mapping cone and then shifted by minus one; this is the same homotopy
argument as the node's signed shifted-coordinate calculation. Order embeddings
of the natural numbers are automatically unbounded, so the ceiling construction
does not require choosing from the theorem's explicit unboundedness hypothesis.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
