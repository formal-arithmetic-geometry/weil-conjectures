## What changed

Proved `AlgebraicGeometry.principalSubsetHorizontalFaces` with its existing signature unchanged.
Added two fully proved modules: `PrincipalOpenCechSubsetHorizontalFaceCoordinate` computes one
ordered face coordinate; `PrincipalOpenCechSubsetRowReassembly` reassembles any family supported
on one row. The original module imports both privately for its proof. All existing public imports
and interfaces remain unchanged. No other existing module is adapted.

The coordinate proof expands the ordered differential, bijects deleted positions with subset
members, counts the sign exponent, checks unsupported singletons vanish, and proves naturality
of section transport and cancellation of the coefficient-degree casts. The reassembly proof uses
a direct finite-sum bijection, not an abstract choice of coordinates or an existence theorem.
The original theorem proves the off-row support condition and combines these two calculations.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.principalSubsetHorizontalFaces`.
Also proved `AlgebraicGeometry.principalSubsetHorizontalFaceCoordinate` and
`AlgebraicGeometry.principalSubsetRowReassembly`. Holes closed: 1. Holes added: 0.
There is no `sorry` in any delivered Lean file, including all private helpers.
This is a proof, not a decomposition leaving lower holes.

Single-file compilation is performed through lcompile.py; the required delivery dry run checks
all three modules and their declarations. The proofs cover empty covers (no source subset),
singleton target subsets (off-row support), oversized rows (empty tuple families), repeated
principal opens, and zero section groups without adding hypotheses.

## No longer needed

None of the original imports or proof-dependency nodes is removed. The two original definition
nodes are still used. No new dependency on `PrincipalOpenCechSubsetInsertionBijective` or
`PrincipalOpenSubsetCechComparison` is introduced: their private coordinate arguments were
read for search, but the final proofs use the actual definitions and finite enumeration tools.
No node is claimed pruned merely because it was considered during proof development.

## Where the brief, the DAG or earlier work was wrong

No statement error or unit-route departure was found. LeanSearch returned an internal server error;
this unavailable search is recorded alongside the successful LeanFinder, Loogle and source searches. The original three-step plan is now
implemented in Lean. The local literature snapshot is absent on this machine; the cited ordered
formula and totalization were read at the Stacks Project URLs recorded in the nodes.

## New nodes

`lem-sc-principal-open-cech-subset-horizontal-face-coordinate` records the proved, single-target
coordinate calculation (the original plan's first two steps), with no total inclusion or insertion.
Its module contains private, proved helpers for enumeration, open transport, restriction
naturality, and coefficient-cast cancellation.

`lem-sc-principal-open-cech-subset-row-reassembly` records the proved generic reassembly of a
family supported in a single row (the original plan's third step). Its finite-sum bijection proof
works for arbitrary row degree and any family satisfying the support and coordinate hypotheses.
No change record is needed: all existing statements and definitions remain unchanged.

## Second reading by B3

1. Compared the delivered item module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof body and proof-only imports were added. Verdict: pass.
2. Compiled all three delivered modules with lcompile.py and checked for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`. No such declarations occur. `#print axioms` for each public theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Read both split-off statements and their proofs and checked the finite edge cases (empty index set, singleton source, empty filtered rows, repeated opens, and zero sections). Each statement is true, strictly simpler than the parent, and has a matching node and source; no duplicate library theorem was found by the recorded searches. Verdict: pass.
4. Checked the proof route from the parent downward. The row reassembly and single-coordinate lemmas are used exactly where the DAG plan places them; no unit step is bypassed, and no import or proof dependency is pruned. Verdict: pass.
5. Checked the three node files against the Lean declarations, including statements, proof steps, `proof_deps`, origins, module paths, and realized split status. They agree with the delivered proofs; the unit route remains represented by the parent node. Verdict: pass.

Changed during second reading: no Lean proof or statement changes were necessary. Added this review section to satisfy the delivery report contract.
