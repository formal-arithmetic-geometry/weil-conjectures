## What changed
Replaced the proof of `Algebra.exists_popescu_admissible_containing_finset` in
`Sheaf.RingTheory.PopescuFlatCoordinatesA0` with a reduction to the localized quotient
setup and the existing `Algebra.exists_directed_artinian_flat_subalgebras`, followed by
finite-set induction in a directed covering family. The existing signature and docstring
are byte-for-byte unchanged. Public imports are unchanged. Added the proof-only import
`Sheaf.RingTheory.PopescuFlatCoordinatesSetup`, whose new module states the remaining
setup theorem; no definitions were introduced or altered.

## Proved and sorry left
Closed the original hole in `Algebra.exists_popescu_admissible_containing_finset` (1 of 1
holes in the item). Added one hole in `Algebra.popescu_flat_coordinates_setup`, with node
`lem-weil-pbc-popescu-flat-coordinates-setup`. There are no other direct holes in the
delivery. This is a decomposition: one upper hole closed and one strictly smaller setup
hole added, net zero holes closed. The existing imported directed-subalgebra theorem is
still open. The item is not claimed to be an axiom-free completed proof.

The setup theorem states only Artinianity, locality, the maximal-ideal identity, and
cotangent-homology finiteness of the explicit prime-power quotient. It does not assert
existence of admissible subalgebras or finite-set containment. Its witnesses are proofs
of properties of a fixed, already constructed ring; no ring data is chosen from an
unproved mere-existence theorem. Its docstring gives the mathematical argument and source.

Both delivered modules compile without errors or non-sorry warnings through lcompile.py.
A scratch-copy `#print axioms` checks the item and setup; only the permitted standard
axioms and `sorryAx` from the remaining statements appear. deliver3.py also performs its
full declaration axiom probe.

## No longer needed
Removed direct proof imports `Sheaf.RingTheory.GeometricallyRegularH1Injective` and
`Sheaf.RingTheory.LocalizationOfRegularRing` from the item. They remain proof imports
of the setup module, so this does not claim either module is pruned from target closure.

The old item proof dependencies no longer used directly are
`def-weil-pbc-flat-ring-map`, `def-weil-pbc-g-ring`,
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-smooth-ring-map`,
`lem-weil-pbc-faithfully-flat-ideal-contraction`,
`lem-weil-pbc-flat-local-hom-faithfully-flat`,
`lem-weil-pbc-geometrically-regular-h1-injective`,
`lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-localization-of-regular-ring`, and
`lem-weil-pbc-noetherian-local-quotient-artinian-local`.
The setup node retains the localization, quotient, and injectivity dependencies;
statement definitions remain in the relevant statement dependencies. The existing
Artinian-flat-subalgebras theorem already supplies subalgebras and their flatness, so the
item needs no separate faithful-flatness or injectivity argument. No global module
pruning is claimed.

The first worker's redundant `Algebra.popescu_directed_subalgebras`, its module
`Sheaf.RingTheory.PopescuFlatCoordinatesDirected`, and its proposed node
`lem-weil-pbc-popescu-flat-coordinates-directed` were removed from the sandbox delivery.

## Where the brief, the DAG or earlier work was wrong
The first worker treated the unused colimit-universal-property universe of the existing
directed-family theorem as requiring a new holed theorem. Explicit universe arguments
`.{u, v, 0}` allow direct use of that theorem. The first worker's new-node records lacked
exact Lean signatures, searches, self-contained statements, and usable proof descriptions;
these were repaired for the one retained setup node. The original node's proof record
was not updated; it now describes the actual reduction and its dependencies.

The setup theorem remains substantial localization and cotangent-finiteness glue. Searches
with different wording found Mathlib's finite-dimensional conormal-space instance and
individual cotangent results, but no theorem of the full setup statement. LeanSearch was
unavailable and was recorded as such. Upstream/library searches also found local quotient
arguments and private geometric-localization helpers, rather than the entire setup.

## New nodes
`lem-weil-pbc-popescu-flat-coordinates-setup`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-flat-coordinates-setup.json`, states
the setup used before applying Tag 07FG. Its three proof steps describe localization,
injectivity and conormal finiteness, then quotient locality/Artinianity and residue-field
transport. Its Lean record is the exact retained signature, and its proof dependencies
are the union of its steps' uses. There are no change records because no existing
statement or definition changed.

## Second reading by E1
1. Compared the delivered existing module against the repository with `diff` and parsed
   declaration comparison. Verdict: the only existing declaration has exactly the same
   signature, byte for byte, and unchanged docstring. No definition or public import
   changed; the edits are its proof and proof-only imports. The setup is a new statement
   in a new module, not a change to the target contract.
2. Compiled both delivered modules locally in dependency order without errors or style
   warnings. Reviewed the sources for forbidden declarations/attributes and hollow
   definitions. Verdict: no axiom, unsafe, opaque, implemented_by, extern, or holed
   definition; only the named setup theorem has a direct sorry. The scratch axiom check
   admits only propext, Classical.choice, Quot.sound and sorryAx. The finite-set induction
   uses the cover of zero to handle the empty case.
3. Reviewed each proposed split statement, searched the library/upstream sources and
   performed real LeanSearch, LeanFinder and Mathlib grep searches. Verdict: the directed
   split was redundant and was removed. The retained setup is true and strictly a part
   of the argument: for n = 1 it is the residue field case; for q = 0 in a domain it is
   the fraction-field case. Primality makes L nonzero, and n ≥ 1 makes J^n proper; the
   excluded n = 0 would give a zero quotient. A positive characteristic of a field is
   prime, justifying the input to Tag 07E5. The residue-field isomorphism respects k,
   and H1Cotangent functoriality transports finite generation. Checked the source online
   at https://stacks.math.columbia.edu/tag/07FH and
   https://stacks.math.columbia.edu/tag/07E5. The statement contains no arbitrary data
   choice: existential Artinian/local witnesses live in Prop.
4. Read from the item downward. Verdict: the directed theorem is now used directly with
   explicit universes, and no new directed-family hole remains. The existing elementary
   finite-set proof is correct and was kept. Unused direct proof imports were removed,
   and every old item proof dependency absent from the new direct route is listed above.
   Reviewed `dag/units/sk-thm-p1.json`: the item is below its realized statement/steps;
   no realized unit node or route is bypassed and the unit record is unchanged.
5. Compared Lean declarations and proof calls with both delivered node records. Verdict:
   exact setup signature recorded; new node has source, full proof steps, three real
   search kinds, creation/blueprint/chapter/unit metadata; item proof and proof_deps now
   match the actual reduction. The directed-family node was deleted with its module.

Second reading changed: eliminated the redundant directed-family theorem/module/node;
fixed universe instantiation; replaced letI with let to satisfy the compiler linter;
removed unused direct imports; supplied the setup proof docstring and complete node
records; updated the item node and corrected the report's accounting to decomposition.
