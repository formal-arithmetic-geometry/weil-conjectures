## What changed

Proved `ringKrullDim_le_of_goingDown_of_surjective` in
`Sheaf.RingTheory.KrullDimension.GoingDown`, preserving its signature.
The proof installs the algebra structure associated to the ring homomorphism,
chooses a prime above the last member of each strict chain by spectrum
surjectivity, and registers the resulting lies-over equality.
Mathlib's `Ideal.exists_ltSeries_of_hasGoingDown` then supplies a strict chain
of the same length upstairs. Taking the supremum of these lengths proves the
inequality via `Order.LTSeries.length_le_krullDim`.

The DAG's finite-chain route is unchanged: its induction is already proved in
Mathlib. No new modules, statements, definitions, or nodes are needed.
All existing public imports are retained: they expose the prime-spectrum
comap, dimension, and going-down APIs used by the public statement. No
proof-only imports are added.

## Proved and sorry left

Closed the sole original hole:
`ringKrullDim_le_of_goingDown_of_surjective`
(node `lem-sc-going-down-surjective-dimension`).
There are no remaining sorries in the item and no added holes.
This is a complete proof from Mathlib, not a decomposition into new statements.
The final file compiles cleanly with `lcompile.py`.
The argument works for independent universes, the zero ring (the chain supremum
is empty), zero-dimensional rings, and unbounded dimension. No nontriviality or
finite-dimensionality assumptions are introduced.

## No longer needed

No imports removed. Each retained import supplies a public-statement API;
the existing public import interface is preserved.
No DAG nodes or Sheaf/WeilConjectures modules are pruned: the existing proof
uses precisely the dimension definition and the stated hypotheses, as planned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. Earlier searches did not identify
`Ideal.exists_ltSeries_of_hasGoingDown`, which proves exactly the recursive
chain-lifting step of the existing plan. The leanfinder search found going-down
APIs, Loogle confirmed this chain-lifting theorem, and source searches of
Mathlib and both library roots confirmed the relevant signatures.
The unit record `sk-thm-br` has no realized statement or step attached to this
item; the proof retains the given chain route and changes no unit route.
The locally absent blueprint section is not used to invent any new argument:
the node and declaration already supply the full sourced chain proof.


## Second reading by W2

1. **Interface and accidental changes.** Compared the delivered module with the repository version; the theorem signature and all existing declarations are byte-for-byte unchanged. The only Lean change is the proof body.

2. **Proof validity.** Compiled `lean/Sheaf/RingTheory/KrullDimension/GoingDown.lean` with `lcompile.py`; it succeeds with no errors or warnings. The proof has no `sorry`, forbidden declarations, or hollow definitions. It uses the Mathlib chain-lifting theorem `Ideal.exists_ltSeries_of_hasGoingDown` and the standard Krull-dimension length bound.

3. **Statements and dependencies.** No statements were added or weakened, and no new nodes or split-off holes are present. The existing node's proof route was updated to describe the actual Mathlib chain construction; its statement and proof dependency remain unchanged. Searches found no pre-existing theorem duplicating this target.

4. **Pruning and route.** All three public imports are needed by the public signature or proof (`PrimeSpectrum.comap`, `ringKrullDim`, and `Algebra.HasGoingDown`/going-down chain lifting), so none can be removed. The unit route and `realized` record are unchanged.

5. **Axioms and edge cases.** The argument handles empty chains, zero-dimensional rings, independent universes, and unbounded dimensions through the supremum formulation. No extra assumptions are introduced; the theorem's axioms are confined to the permitted Mathlib foundations.

**Changes made:** updated the DAG proof metadata to match the delivered Mathlib proof and added this second-reading record.
