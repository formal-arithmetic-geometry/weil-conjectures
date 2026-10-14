## What changed

The only Lean change expands `rwa [hw] at hp` into `rw [hw] at hp` followed
by `exact hp`, making the final transport explicit. Verified that it compiles. This assignment is an audit of an already repaired item:
the current core is the general finite-morphism flat-test descent theorem, rather
than the false normalization statement mentioned in the repair queue.

The proof lifts each point over x to the test pullback, descends stalk flatness
through the flat local (hence faithfully flat) projection, then uses the finite
flat target locus and restriction stalk isomorphisms. Both proof dependencies
are used, and the node already records exactly this route.

## Proved and sorry left

AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core is already
proved in the supplied repository. The sandbox module compiles without
warnings. There were zero sorries initially; zero holes closed, zero added, zero
split off, and zero remaining in the item. This delivery claims no new proof progress.
Node: lem-sbc-stalk-normalization-depth-two-section-flat-core.

## No longer needed

None. The proof uses both FiniteFlatTargetLocus and
WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic. The three public
Mathlib imports provide the statement's scheme, Noetherian, flat, and finite API.
No dependency node, module, or unit step is pruned by this audit.

## Where the brief, the DAG or earlier work was wrong

The assignment says the module still contains sorry, but the current module has
none. coord/repairs.txt still repeats upstream review #1428 against the former
normalization-only statement. The landed change record
coord/changes/stalk-normalization-depth-two-section-flat-core.md already replaces
that false statement by this descent core and adapts its caller.

The normalization caller GaloisCover.stalk_normalization_depth_two_section_flat
explicitly takes the rational generic-section point hZ and passes it to
GaloisCover.exists_stalk_normalization_split_formal_test. It obtains the flat
pullback from that split test before applying this core. Consequently this core
does not infer flatness from depth two alone. No further signature change,
forced adaptation, new node, or change record is needed.

## Second reading by W4

1. Compared the entire delivered module with the read-only repository using diff.
   The signature, visibility, definitions, documentation, and imports are identical.
   The initial sandbox had only a proof expansion (`rw [hw] at hp; exact hp`)
   relative to the repository's `rwa [hw] at hp`. Retained this explicit transport
   proof after compiling both forms; all text outside that proof is unchanged.
   No new interface change or change record is required.
2. Compiled the sandbox module successfully without warnings. Compiled a scratch
   copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`:
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Read the whole proof: no sorry, forbidden declaration, hollow definition, or
   data selected from an unproved existence theorem. Verdict: sound proof.
3. No statements were split off, so no new-node or duplicate-statement checks
   arise. Checked the theorem mathematically: no surjectivity of the test is
   needed, since the specified b lifts each point of the fibre over x. An empty
   fibre makes the stalk condition vacuous; an empty source gives the entire
   target flat locus. An empty test cannot supply b. Verdict: no false edge case.
4. Read both dependency declarations and searched the scheme flatness/descent
   API and existing Sheaf proofs with flat-descent and faithful-flatness terms.
   The existing proof directly applies the source-library algebra descent theorem
   and finite flat target locus; both proof-only imports are used. The public
   imports supply the signature's Noetherian, finite, and flat API. Nothing in
   the current proof_deps is unused, so no pruning is claimed. The unit
   sk-prop-input-spreading retains its formal-test then descent route, and its
   file is unchanged. Its realized lists are already empty in the repository;
   this is an existing bookkeeping gap, not a route change in this delivery.
5. Read the node's statement, Lean signature, proof steps, proof_deps, and
   proof_origin against the proof. They agree: pullback-point lifting, local
   faithful flatness, algebra descent, then the finite open target locus and
   restriction stalk isomorphisms. No node changes are necessary.

Second-reading changes: recorded this independent review; retained the worker's
explicit transport proof. An initial dry run of the byte-identical repository
proof was refused because the item module must change; the delivered expansion
is the worker's original, checked proof-only change, not a new theorem or hole. This is an audit of one already proved theorem: zero holes
closed out of zero initial holes; zero holes added or split off; no modules pruned.
