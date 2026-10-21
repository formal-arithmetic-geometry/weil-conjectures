## What changed

Filled the three original proof obligations in `Sheaf.Paper.ConstantWeilStructure`.
The regular coefficient complex is K-flat by the tensor unitor, and its terms are
flat units or zero objects. The independent-coefficient tensor comparison gives
the required site-flatness.

Constructed the strict chain unit using the actual finite reduction tensor sections
and pullback adjunction units. Their compatible product defines a mapping-cocone
lift with zero shifted component. Unit sections at terminal objects determine maps
out of the regular single complex, proving the prescribed uniqueness.

Identified each finite pullback level with the finite regular module, respecting
its normalized generator. The induced tower identification respects transitions
because the coefficient projections are epimorphic. Evaluation identifies the
limit with the completed regular module. Local lifts from the valuation ring show
surjectivity of the projections; the existing epimorphic-tower theorem makes
1-shift epic. The kernel-fork and short-exact mapping-cocone calculation then
proves the specified unit is a quasi-isomorphism.

All existing public definitions, signatures, docstrings and public imports are
retained. Added proved private helpers and private proof imports. The DAG proof
and dependencies record the implemented argument. No new modules are delivered.
The proof-support scope commands and local attributes are documented in
`coord/changes/constant-weil-structure-proof-scopes.md`; preflight requested this
record even though all original public signatures and definitions are unchanged.

## Proved and sorry left

Closed all three original holes:

- `WeilConjectures.constantWeilIntegralComplex_good`.
- `WeilConjectures.constantWeilChainUnit_existsUnique`.
- `WeilConjectures.constantWeilChainUnit_isIso`.

Added zero holes and split off zero holes. The item has zero remaining `sorry`.
All three obligations remain attached to `def-weil-constant-weil-structure`.
The six previously proved obligations are retained. The complete item compiled cleanly
in 41.5 seconds with the original public signatures.

## No longer needed

No original imports, declarations, nodes or modules were withdrawn. No assigned
unit route is bypassed. The good-complex proof needs no resolution construction:
the tensor-unit argument proves K-flatness directly. Finite-level generator
naturality and the epimorphic-tower theorem supply the strict Roos argument.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The DAG's open-obligation description
is replaced by the implemented proofs. The proof needs explicit transport through
the scalar-extension witness and the actual pullback adjunction; no arbitrary
comparison map or coefficient witness is chosen.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
