## What changed

No Lean statement, definition, proof term, or import changed. One proof comment now
clarifies that `hb` lifts every point of the fibre once the caller supplies pullback flatness. The dispatched item already contains
an explicit complete proof of
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`.
Copied that module into the sandbox and compiled it successfully with lcompile.py (3.5 seconds).
This report audits the still-listed repair for upstream review #1428: the current core is the
corrected flat-test descent statement, not the false normalization-only statement.
The landed change record is `coord/changes/stalk-normalization-depth-two-section-flat-core.md`.

The proof lifts each pair of fibre points to the pullback. Its projection stalk map is flat
and local, hence faithfully flat; the pullback identity supplies flatness of the composite.
`Module.Flat.of_flat_of_faithfullyFlat` descends this to the original stalk map.
`isOpen_setOf_finite_flat_stalks` then supplies an open target neighbourhood, and restriction
stalk isomorphisms prove flatness on that neighbourhood. Neither depth two nor generic
splitting is assumed to imply flatness within this core: pullback flatness is an explicit
hypothesis. The normalization caller retains its rational generic-section hypothesis `hZ`
and passes it to the formal-test theorem before invoking the core.

## Proved and sorry left

Existing proved declaration verified:
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
(node `lem-sbc-stalk-normalization-depth-two-section-flat-core`).
The assigned module has zero sorries on arrival and zero after verification.
Holes closed by this delivery: none. Holes added: none. No new declarations.
The node already records a prior proof landing on 2026-10-14.
An explicit scratch-copy `#print axioms` check returned exactly `propext`,
`Classical.choice`, and `Quot.sound`; the delivery dry run also supplies the standard probe.

## No longer needed

None. Both proof imports are used: `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus`
and `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
Both recorded proof dependencies remain necessary. No nodes or modules are pruned.
No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dispatcher brief says this module still contains sorry, but the checked-out module is
already proved and compiles. The outstanding coord/repairs.txt entry describes the original
false normalization-only statement. Its interface correction and the rational-point
requirement in the unchanged caller are already present in the current sources.
This is verification of an already-landed repair, with no claimed new proof progress.


## Second reading by K4

1. PASS: diffed the only delivered module against the repository. The only difference
   is one proof comment. Every existing signature, docstring, definition and import
   is byte for byte unchanged; there are no new declarations or change records.
2. PASS: independently compiled the module with lcompile.py, without errors or warnings.
   Scanned for forbidden declarations and sorry: none. A scratch-copy `#print axioms`
   of `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
   returned only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Read the pullback lifting, composition identity, faithful-flat stalk descent,
   open target locus, and restriction-stalk isomorphism arguments.
3. PASS: no statements were split off, and no data is chosen from an unproved existence
   theorem. The flat test need only meet x: each source point over x lifts to its
   pullback with b. An empty source makes the target locus all of L, so the argument
   also handles that case; an empty test cannot supply b.
4. PASS: searched LeanFinder using a different flat-base-change descent query and
   searched the Mathlib flat-morphism module and local Sheaf sources. No shorter
   existing theorem was found. The three public imports supply statement notions;
   the two plain imports supply the two actual proof dependencies. No obsolete
   proof dependencies or imports remain. Read dag/units/sk-prop-input-spreading.json:
   the formal-test descent is part of its depth-two local computation, not a bypass.
   Its realized fields were already empty and remain unchanged; this is pre-existing
   bookkeeping, not a route introduced by this delivery.
5. PASS: read the existing node, including its current statement, proof steps,
   proof_deps and proof_origin. The two steps match the Lean: faithfully flat
   algebra descent, then finite target-locus openness and restriction. No node edits
   or new nodes are needed. The prior interface change is already documented in
   coord/changes/stalk-normalization-depth-two-section-flat-core.md; it is not part
   of this delivery. The normalization caller explicitly supplies its rational
   generic-section data to the formal-test theorem before invoking this core.

Second-reading changes: corrected the report's inaccurate claim of no comment change,
recorded the independent compile and explicit axiom result, and added this review.
No Lean repair was needed. This verifies one existing proved theorem and closes zero
new holes; zero holes are split off, and no modules are pruned.
