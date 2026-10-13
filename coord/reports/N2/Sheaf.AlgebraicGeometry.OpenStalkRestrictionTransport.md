## What changed

Proved `AlgebraicGeometry.Scheme.exists_openStalk_restriction_transport` in
`Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport`, preserving its signature and visibility.
Added the proof-only import `Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison`.
Three fully proved private helpers establish descent of natural isomorphisms along an
adjunction with invertible counit, composition of slice restrictions, and the transported
restriction/pushforward adjunction. The main proof chooses the existing stalk comparisons,
descends the composite of the required comparison with the inverse of the given comparison,
and cancels the inverse pair. Updated the node proof, proof dependencies, and proof origin.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.exists_openStalk_restriction_transport`
(node `lem-sc-open-stalk-restriction-transport`). One of one original holes proved;
zero holes added, zero holes split off, and no sorry remains in the delivered module.
All three private helpers are proved. The imported comparison theorem already has a complete
proof. No unproved existence theorem is used to choose data.

The module compiles with the prescribed lcompile tool, without warnings. The equal-open case
is included in the adjunction triangle identity and the identity component of restriction
composition; no strict inclusion, nonzero module, or finite-presentation assumption is used.

## No longer needed

Pruned proof dependency `new-module-restriction-stalk-components` and its module
`Sheaf.Algebra.Homology.ModuleRestrictionStalkComponents` from this node's route.
It was not imported by the original item, so no original import was removed.
The auxiliary component/germ construction, canonical comparison composition calculation,
and separate automorphism adjustment are unnecessary: any chosen family of stalk comparisons
works by direct categorical descent. This only prunes this node's dependency edge; other
users of the component module can still need it.

A trial import `Mathlib.CategoryTheory.Adjunction.FullyFaithful` was removed as redundant;
the required Mathlib adjunction infrastructure is available through the existing public import.
The original public import `Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor` remains necessary
for the statement. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was valid but stronger than necessary. Canonical comparisons and
their germ-composition law are unnecessary for this existential theorem. Instead descend
the entire composite isomorphism along restriction using the invertible counit. This proves
the arbitrary-comparison compatibility directly. No statement or definition was changed,
and no forced adaptation or new node is needed. The three elementary private helpers contain
no residual proof obligations.

The comparison and adjunction sources were checked at Stacks Tags 00A0 and 0096. Searches
via leanfinder, loogle and Mathlib/library grep found the existing restriction comparison and
adjunction infrastructure; none was an exact theorem for the whole transport statement.

The earlier attempts were blocked by a style warning in the delivery tool's generated
axiom probe. On this retry the prescribed dry run prints OK: the proof compiles and
passes preflight except for the second reading, which is reserved for the next worker.
No delivery tool or linter setting was modified, and nothing was pushed.

## Second reading by N2

1. **Interface unchanged.** Compared the delivered module with the repository version: the public theorem signature and all existing declarations are byte-for-byte unchanged; only a proof-only import, private helpers, and the theorem proof were added. The node statement matches the Lean theorem.
2. **Proof and axioms.** Compiled the module and the sandbox import closure with `lcompile.py`; compilation is clean with no warnings. The theorem's axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`s, axioms, unsafe declarations, or hollow definitions.
3. **Statement audit.** The theorem remains the original transport assertion, with no added hypotheses or weakened conclusion. The existing comparison dependency is used, and the private descent and adjunction helpers are strictly internal proof steps; no new split-off statement or node was introduced.
4. **Shortest route and pruning.** The proof uses direct adjunction descent and the existing comparison theorem. The unused component/stalk dependency is removed from the node route, while the unit's restriction-composition and transport steps remain represented. The proof-only comparison import is minimal for the proof.
5. **DAG and unit agreement.** Checked the node's `proof`, `proof_deps`, and `proof_origin` against the actual proof and imports; they agree, and no unit statement or realized step is bypassed.

I changed only this report section; no Lean source, node, or change record required repair.
