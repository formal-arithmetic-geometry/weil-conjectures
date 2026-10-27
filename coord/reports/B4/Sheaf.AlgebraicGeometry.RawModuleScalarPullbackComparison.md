## What changed

The current item is already P2's zero-hole compatibility module for the canonical
upstream construction. Added three fully proved theorems in
`AlgebraicGeometry.Etale.RawModuleScalarComparison`: `pullback_unit`,
`eq_pullback_of_unit`, and `kanSheafification_eq_pullback`.
A proof-only `import all` of `RawModuleScalarSheafComposition` supplies its
already-proved private scalar unit identity; its public composition theorem is not used.
The first two give the defining adjunction equation and its uniqueness. The third
retains in the library the equality between the particular canonical comparison and
the explicit Kan-extension/sheafification composite. The earlier delivery checked
this equality only in scratch code.

Updated `def-sbc-raw-module-scalar-pullback-comparison`'s proof, proof origin and Lean
note to identify the retained proof. The upstream construction attachment, statement,
proof dependencies and unit route are preserved. Existing definitions, signatures,
instances and public imports are untouched. No source-library module is edited.

Change record: `coord/changes/B4-raw-scalar-canonical-formula.md`.

## Proved and sorry left

The item starts with 0 holes. Holes closed: 0 of 0. Holes added: 0. Split off: 0.
Sorries left: none. This is construction verification, not a proof-count gain.

The final module compiled through `LCOMPILE_NO_LOCAL=1 lcompile.py` with exit code 0,
no Lean diagnostics and a reported compile time of 19.4 seconds. The delivery tool
performs the final axiom probes and preflight before pushing.

New complete proofs, with namespace
`AlgebraicGeometry.Etale.RawModuleScalarComparison`:

- `pullback_unit`.
- `eq_pullback_of_unit`.
- `kanSheafification_eq_pullback`.

The formulas are uniform in every commutative coefficient ring and scheme morphism.
No nonzero, nonempty, torsion or finiteness hypotheses are added; zero rings, empty
schemes, zero sheaves and identity morphisms remain covered by the same unit equations.

## No longer needed

None. No imports, nodes, modules or unit steps are pruned. The compatibility path
remains available to all live and quarantined consumers. The canonical construction
and exact forgetting API are reused without duplicating their data.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a repeatedly split proof obligation. The present source
instead has the zero-hole canonical-construction migration already landed by P2.
Repeating that migration would be a no-op. This delivery retains its missing library
verification: the equality previously supplied only by a scratch regression is now a
named, complete theorem available from the compatibility module itself.

The proof reads the existing dependency signatures first and follows the adopted
ModuleAbelianInverseImageComparison argument and the current blueprint's unit
calculation. Loogle, LeanFinder and msearch grep were run for the comparison and
unit-factorization APIs. No new mathematical dependency or node is required: all
three theorems verify the existing construction node.

The published server build initially exposed the older explicit Kan-extension comparison,
while the shared sources contained P2's newer canonical alias. A server-side definition
probe confirmed this. Reusing the existing proved scalar-unit identity avoids relying on
that implementation difference. The full formula proof computes only the explicit
composite's unit equation and applies uniqueness; it does not unfold the comparison's
implementation. The import-direction check confirms that the private proof import
creates no Lean import cycle.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
