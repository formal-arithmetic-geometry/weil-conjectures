## What changed

Replaced the sorry in `exists_restrict_homotopyEquiv_single_of_stalk` by a complete
Lean proof from two strictly smaller statements, without changing its signature.
Added proof-only imports of `FiniteFreeStalkChainMapPairLift` and
`FiniteFreeStalkHomotopyPairShrink`, with a new module and node for each.
Updated the parent node's proof, proof_deps and proof_origin to match Lean.

The first new statement lifts arbitrary prescribed chain maps without any inverse
condition. The second spreads homotopies of already fixed endomorphisms; it does
not produce chain maps. The main proof transports the given stalk homotopies,
shrinks for the two identities, constructs the homotopy equivalence, and transports
it across the natural comparison for successive restriction.

## Proved and sorry left

Closed (by decomposition, not an independent sorry-free proof):
`AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopyEquiv_single_of_stalk`
(node `lem-pc-finite-free-stalk-homotopy-spread`).
No sorry remains in the item module.

Added two holes, each the exact body `:= by sorry`:

- `AlgebraicGeometry.Scheme.Modules.exists_restrict_chainMap_pair_of_stalk`
  (node `lem-pc-finite-free-stalk-chain-map-pair-lift`).
- `AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_pair_of_stalk`
  (node `lem-pc-finite-free-stalk-homotopy-pair-shrink`).

Each new theorem has its complete finite matrix proof in its docstring and node.
All three modules compile together in import order with lcompile.py.
Ranks zero, degree i outside [0,d], zero complexes, and nonreduced schemes were
checked mathematically: the proofs require germ equality, never germ injectivity,
and off-support components are forced by zero objects. Empty schemes have no y.

## No longer needed

No existing node or module is pruned. The unused Homotopy import was removed
from the new chain-map lifting module. The original module had no
proof-dependency imports to prune and its node
had no proof_deps. All original public imports are retained; both new proof-only
imports are used. The finite matrix route and the unit's route are preserved.
No node or module is made unnecessary by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The node was marked split with no proof dependencies, although its two substantial
finite matrix steps had no stated declarations. Those steps are now the two named
new statements; the categorical assembly is fully proved in Lean.

The referenced blueprint source file is absent from this machine's literature
checkout, and an attempt to read the pinned public raw source returned no file.
The new proofs in words expand the supplied DAG's numbered finite matrix argument
and are explicitly attributed to an agent. No new literature argument or different
proof route was introduced. LeanSearch returned Internal Server Error for both
new statements; semantic, type-pattern and source searches found no match.

## New nodes

`lem-pc-finite-free-stalk-chain-map-pair-lift` states exact lifting of a prescribed
pair of chain maps on a common neighbourhood, with complex isomorphisms comparing
stalk pullbacks. This is the coefficient and chain-equation part of steps 1–2.

`lem-pc-finite-free-stalk-homotopy-pair-shrink` states spreading of homotopies of
two fixed endomorphism pairs after further shrinking. This is the remaining
homotopy-coefficient and homotopy-equation part of steps 2–3.

No statement or definition was changed and no change record is needed.

## Second reading by U1

1. Compared the item module against the repository version. The theorem signature and all
existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body
were added. The two new modules contain new declarations explicitly covered by the two new DAG
nodes. Verdict: pass.

2. Compiled all three delivered modules with lcompile.py. They compile without errors. The item
has no sorry; the two split-off declarations have exactly `:= by sorry`, and no definition contains
sorry, axiom, unsafe, opaque, extern, or implemented_by. Their remaining sorryAx use is confined
to the named split statements. Verdict: pass.

3. Reviewed both split-off statements and searched the repository and LeanSearch for existing
matches. The chain-map statement lifts arbitrary prescribed maps and imposes no inverse condition;
the homotopy statement fixes both endomorphism pairs and only spreads their homotopies. They are
strictly smaller than the item and have complete finite-matrix proofs in their docstrings. Edge
cases (zero ranks, unsupported degrees, zero complexes, and nonreduced schemes) remain valid.
Verdict: pass.

4. The item proof follows the shortest available route in this library: lift maps, transport the
stalk homotopies, shrink for the two fixed composite pairs, then assemble and transport the
HomotopyEquiv. Both new imports are proof-only and used; no old proof dependency is unused, and
no module can be pruned. Verdict: pass.

5. The item and both new nodes agree on declarations, statements, proof steps, dependencies,
source, and proof origin. The proof keeps the unit route through the finite matrix lifting and
homotopy shrinking steps. Verdict: pass.

I changed only this report section; no Lean statements or definitions were changed during the
second reading.
