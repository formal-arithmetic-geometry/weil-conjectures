## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.exists_restrict_chainMap_of_stalk_eventually`
by an explicit two-step reduction: obtain a chain map on one open, then restrict that map to
smaller opens while preserving its prescribed stalk equation. Its signature and the original
public imports are unchanged. The two new modules are imported privately for the proof.

Added `FiniteFreeStalkChainMapLiftLocal.lean` and `FiniteFreeStalkChainMapLiftRestrict.lean`.
The second reading expanded their source/proof docstrings, repaired their copied node
statements and dependency plans, and removed the restriction module's unused public import
of `Mathlib.Algebra.Homology.Embedding.CochainComplex`.

## Proved and sorry left

Hole closed in the item's module:
`AlgebraicGeometry.Scheme.Modules.exists_restrict_chainMap_of_stalk_eventually`.

Holes added, both public named theorems with complete natural-language proof docstrings:

- `AlgebraicGeometry.Scheme.Modules.exists_chainMap_of_stalk_local`,
  node `lem-pc-finite-free-stalk-chain-map-lift-local`: construct a map on one open only.
- `AlgebraicGeometry.Scheme.Modules.restrict_chainMap_of_stalk_local`,
  node `lem-pc-finite-free-stalk-chain-map-lift-restrict`: preserve an already constructed
  map on smaller opens, with no boundedness or freeness assumptions.

This is a decomposition, not a completed proof free of sorry. One upper hole is closed and
two lower holes are added (net -1 holes closed); no modules are pruned. The three scratch
`#print axioms` checks each returned exactly `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx`. Neither new hole was closed during the second reading; the remaining
restriction argument requires formal comparison coherence, not just naturality in objects.

## No longer needed

No import was removed from the original item. Its old direct proof dependencies
`def-pc-stalk-restriction-complex-iso`, `def-weil-pbc-free-module`,
`def-weil-pbc-module-stalk`, and
`lem-weil-pbc-open-immersion-module-pullback-restriction` are replaced in the item's
`proof_deps` by the two split nodes. All four remain necessary below those nodes or in
statement dependencies; none is claimed as globally pruned. The new restriction module's
redundant public Mathlib cochain-embedding import was removed and the set recompiled.

## Where the brief, the DAG or earlier work was wrong

The first worker copied the target's full natural-language statement and proof into both
new nodes, including finite-free construction steps in the restriction-only node and
hereditary restriction in the one-open node. Those records did not describe their Lean
statements. They also copied the parent's review certifications into the new nodes; those
were removed. The short docstrings were descriptions, not complete proofs. The second
reading repaired these faults and corrected the report's progress accounting.

## New nodes

`lem-pc-finite-free-stalk-chain-map-lift-local` retains exactly the target's boundedness,
finite-free-or-zero assumptions and prescribed stalk map, and concludes existence on
one open. Its proof plan comprises finite matrices, representative sections and vanishing
of finitely many chain-equation defects. It omits restriction to arbitrary smaller opens.

`lem-pc-finite-free-stalk-chain-map-lift-restrict` assumes one local map with the required
stalk equation and concludes its hereditary representability. Its proof plan constructs
the smaller-open map using restriction-composition and proves the stalk equation by
pullback coherence. It assumes no bounds or freeness. No change records are needed:
no existing statement or definition changes.

## Second reading by G1

1. Compared every delivered module to the repository version. The item is the only
   existing module; its declaration signature is byte-for-byte identical (checked by
   extracting the text before `:= by`). Its only changes are the two private proof
   imports and the proof body. The other two modules and nodes are new. No definition
   or existing statement changes, and no change record is required. Verdict: pass.
2. Compiled all three modules in import order through lcompile.py before and after
   repair. Each compiles without diagnostics. Each scratch copy's `#print axioms`
   returned only the three standard axioms and the expected `sorryAx`. The only
   source holes are exactly the two listed named theorems with `:= by sorry`.
   There are no definitions or forbidden declaration forms. Verdict: pass as a
   decomposition; this is not a closed-axiom proof of the item.
3. Read both split signatures and tested zero complexes, zero ranks, empty or
   disjoint support intervals, a one-term finite free complex (a finite matrix),
   and V = U. The local statement uses boundedness to leave finitely many coefficients
   and chain defects, and zero-germ shrinking makes the defects vanish. The restriction
   statement uses an existing fU and categorical composition, independently of ranks
   and bounds. Each is strictly one part of the original proof, and neither has the
   target's hypotheses and conclusion. Repeated searches with different phrases through
   LeanFinder, Loogle and rg found matrix/germ and composition ingredients, but no
   existing local-extension or hereditary-stalk-equation theorem. The pair-lift theorem
   already imports this item, so it cannot be used without a cycle. Verdict: true,
   needed intermediate statements, with repaired complete proof docstrings and nodes.
4. Read the target downwards and kept the explicit two-step reduction. All original
   imports occur in the statement or its definitions; the new imports are proof-only.
   Removed the new restriction module's unused embedding import. The original four
   proof dependencies are explicitly accounted for above, with no false pruning claim.
   Read `dag/units/sk-thm-picard-perfect.json`: this is a tool argument within the
   finite-free cancellation/spreading step, not a replacement of that unit's route.
   Its realized field is unchanged (already empty in this checkout); no realization
   is removed. Verdict: route preserved, no modules pruned.
5. Read all three node files. The item names exactly the two theorem applications in
   its Lean proof. The new local node now states one-open existence and carries only
   the finite-matrix construction steps. The new restriction node now states stability
   conditional on fU, drops the irrelevant free-sheaf statement dependency, and records
   only restriction/coherence. Their proof_deps are the union of their steps' uses.
   Their proof_origin, source, searches, chapter, unit, blueprint origin, creation and
   verbatim Lean records agree with the delivered modules. Removed inherited review
   certifications from both new nodes. Verdict: pass after repair.

Changed during this reading: both new node statements/proof plans and source locations,
source/proof docstrings and module headers, independent search records, redundant
restriction import, inherited certifications, and the report's decomposition/pruning
accounting. The original item's proof and signature were kept.
