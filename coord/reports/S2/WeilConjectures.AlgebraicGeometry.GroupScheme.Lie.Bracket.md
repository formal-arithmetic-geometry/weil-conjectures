## What changed
Completed three proofs in
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` without changing any signature,
definition, visibility, or import.

`commutator_mem_mixedPoints` computes the two cross-axis restrictions of the projections,
uses the infinitesimal-point kernel conditions, and maps the commutator through each
precomposition homomorphism. In each restriction one factor becomes the identity.

`infPointsMap_infBracket` applies the mixed-point equivalence, uses its inverse identities
to identify the mixed terms with commutators, and uses the group homomorphism's preservation
of products and inverses.

`infBracket_mem_range_infPointsMap` takes the commutator preimage supplied by the hypothesis.
Cancellation against the monomorphism proves that this preimage is mixed. The inverse of
`mixedEquiv` then supplies the required infinitesimal point, and its image equals the bracket
by the mixed-point equivalence's injectivity.

Validation: all three proofs compile together using `lcompile.py`, with no warnings.

## Proved and sorry left
Closed three original holes:
- `AlgebraicGeometry.GrpObj.commutator_mem_mixedPoints`.
- `AlgebraicGeometry.GrpObj.infPointsMap_infBracket`.
- `AlgebraicGeometry.GrpObj.infBracket_mem_range_infPointsMap`.

Added zero holes and split off zero statements. These proofs still depend on the existing
`AlgebraicGeometry.GrpObj.toMixed_bijective` through `mixedEquiv`; this is not a claim that the
resulting declarations have no transitive sorry dependencies.

Six original holes remain unchanged. The tool groups the instance fields under these labels:
- `instance instance : LieRing (Lie G)` (four holes).
- `instance instance : LieAlgebra Γ(S, ⊤) (Lie G)` (one hole).

Individual remaining holes:
- `AlgebraicGeometry.GrpObj.toMixed_bijective` (mixed-point identification, `sk-d-tangent`).
- `AlgebraicGeometry.GrpObj.instLieRingLie.add_lie` (instance field, `sk-d-tangent`).
- `AlgebraicGeometry.GrpObj.instLieRingLie.lie_add` (instance field, `sk-d-tangent`).
- `AlgebraicGeometry.GrpObj.instLieRingLie.lie_self` (instance field, `sk-d-tangent`).
- `AlgebraicGeometry.GrpObj.instLieRingLie.leibniz_lie` (instance field, `sk-d-tangent`).
- `AlgebraicGeometry.GrpObj.instLieAlgebraLie.lie_smul` (instance field, `sk-d-tangent`).

The existing node `def-wf-lie-algebra-derivation` records the bracket module's open declarations
in its Lean audit. No new node is needed for these proof-only changes.

## No longer needed
No imports removed and no nodes or modules pruned. The three proofs use only the module's
existing dependencies and preserve the existing mixed-commutator route.

## Where the brief, the DAG or earlier work was wrong
No mathematical statement error found. The first dry run required exact instance labels
in the report; those labels are now included. The wrapper permits the independent second
reading to remain absent at the worker's dry-run stage, as the brief requires.

The DAG attaches the module through audit records,
rather than through a primary `lean.module` entry for each of these three declarations.

During testing I accidentally edited the read-only repository's copy of the item. I restored
its original proof text before continuing in the sandbox. The delivery contains only the
sandbox's proof changes.

## Second reading by S2

1. Compared the delivered module with the repository version using `diff`. All existing
   declaration signatures, definitions, visibility, and imports are byte-for-byte unchanged;
   only the three theorem proofs differ.
2. Compiled the complete sandbox import order with `lcompile.py --all`; it succeeds without
   errors or warnings. No forbidden declarations occur. The remaining `sorry`s are exactly the
   six named declarations listed above, and no new `sorry`s were added.
3. Checked the three proof routes against the declarations used in the module and the relevant
   DAG audit. Each proof is a direct consequence of the mixed-point equivalence, group
   homomorphism laws, and monomorphism cancellation. No split-off statement or new node was
   introduced, and no duplicate library theorem was added.
4. The proofs retain the unit's mixed-commutator route through `toMixed_bijective` and
   `mixedEquiv`. All existing imports are used by statements or proofs, so there is no import
   or proof dependency to prune.
5. The node audit and report agree with the Lean file: the three listed declarations are closed,
   `toMixed_bijective` and the Lie structure fields remain open, and the proof dependency route
   is unchanged.

I changed only the three proof bodies and added this second-reading record; no statement,
 definition, import, node, or change record required repair.
