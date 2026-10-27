## What changed

Proved `AlgebraicGeometry.exists_finitePresentation_chain_stage` in
`Sheaf.AlgebraicGeometry.FinitePresentationChainDescent`, retaining its signature
and public imports. Added private proof imports and proved private helpers for
arrow descent, pullback transport, eventual base-change properties, and qcqs
finite coproducts. No other Lean module is changed.

The proof descends the three vertex families together, retains the prescribed
model of E by pullback, and descends all edges over the base. It applies the six
existing property-descent declarations and takes one common stage. The final
assembly constructs the canonical target pullback, both chain compatibility
equations, and the coproduct cartesian comparison explicitly. Finite filters and
coproducts include the empty family. The DAG proof record follows this assembly.

Validation: the complete module compiled through `lcompile.py` in 11.0 seconds,
with no errors or warnings. All proof imports supply declarations used by this
proof; the original statement and public imports are unchanged.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_finitePresentation_chain_stage`
(node `lem-weil-pbc-finite-presentation-chain-descent`).
No holes added or split off. The item and all its private helpers contain zero
`sorry`s. Existing proof-dependency holes are unchanged.

## No longer needed

No original Lean imports removed and no modules withdrawn.
The item's proof no longer needs
`lem-weil-pbc-finite-presentation-equalities-descent`
(`Sheaf.AlgebraicGeometry.FinitePresentationEqualitiesDescent`). Descended edges
are constructed as morphisms over the base; this supplies the structure-map
equations directly. The existing arrow descent lemma supplies compatibility with
the original limit arrows. Thus no further eventual equality is needed.
All other original proof dependencies remain used. No unit statement or realized
unit proof step is bypassed. This is pruning of this node's proof dependency,
not a claim that the equality-descent module is globally unused.

## Where the brief, the DAG or earlier work was wrong

The planned equality-descent step is unnecessary for this chain-shaped diagram:
there are no independent relations between paths to impose after descending the
edges as base morphisms. The proof must also account for the nested pullbacks of
the prescribed E model; horizontal pasting supplies its canonical comparison
with the exact target pullback in the original statement.
No statement or definition repair was required. No new nodes or change records.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
