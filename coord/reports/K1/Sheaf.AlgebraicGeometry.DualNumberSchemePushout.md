## What changed

Proved `AlgebraicGeometry.existsUnique_dualNumberScheme_extension` in
`lean/Sheaf/AlgebraicGeometry/DualNumberSchemePushout.lean`, preserving its signature and
existing docstring. Added the proof-only import `Mathlib.AlgebraicGeometry.Stalk` for the
existing dependency `lem-weil-pbc-morphism-from-spec-local-ring`.

The proof follows all three steps of the existing node. The unit criterion for a
square-zero extension proves locality and locality of the residue and projection maps.
The common field restriction identifies the closed points. Mathlib's local-spectrum
correspondence supplies local stalk maps at that common point and makes equality of
residue restrictions an equality of ring maps. The assembled ring map sends an element
to its common constant coefficient and its tuple of infinitesimal coefficients; all
ring-homomorphism laws and projection identities are proved explicitly. Applying Spec
constructs the extension. For uniqueness, one projection identifies the closed point,
then all projections identify the candidate's stalk map coefficient by coefficient.

Four private proved helpers support this calculation. The three locality helpers are
used only as local instances inside the theorem proof. No public declaration, public import, definition,
statement, or global instance was added or changed. The DAG route and dependencies
already describe this argument, so no node modification is needed.

Searches were run through msearch.py with LeanFinder (square-zero finite gluing), Loogle
(SpecToEquivOfLocalRing), and grep (local-spectrum and pushout ingredients), and with rg
on both library roots and Mathlib. The useful result is the already planned Mathlib
local-spectrum equivalence, not a shorter ready-made pushout theorem. Read the pinned
Stalk.lean correspondence, square-zero unit criterion and map formulas, and Stacks
https://stacks.math.columbia.edu/tag/0B2B (the local literature file is absent here).

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.existsUnique_dualNumberScheme_extension`
(blueprint: `lem-sc-dual-number-scheme-pushout`).

No sorry remains in the item's module. No hole was added or split off, and the proof uses
only Mathlib results, with no dependency on a holed project theorem. This is a proof,
not a decomposition. Single-file compilation through lcompile.py checks the complete
construction and uniqueness argument. The deliver3.py dry run also checks declaration
axioms and the delivery preflight.

The construction handles n = 1 and n = 2 uniformly; `hn` is used exactly to select a
coordinate for the common constant term and to identify the closed point in uniqueness.
No assumption about algebraic closedness, characteristic, or an affine target is used.

## No longer needed

None. All original public imports are needed by the unchanged statement, and the sole
added proof import realizes the existing Mathlib dependency. Both planned proof
dependencies (`def-sc-dual-numbers` and `lem-weil-pbc-morphism-from-spec-local-ring`)
are retained. No node, module, or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The original module did not yet import
Mathlib.AlgebraicGeometry.Stalk although its node lists the local-spectrum correspondence
as a proof dependency. The proof-only import supplies it. The repository's cited local
Stacks source file is absent on this machine; its tag was read online instead.


## Second reading by K1

1. PASS: read the complete repository/sandbox diff. The existing public theorem
   signature is byte-for-byte identical (also checked by extracting the text before
   `:= by`). Its docstring and three public imports are unchanged. The additions are
   four private proved helpers, a proof-only Stalk import, and the theorem's proof.
   No definition, target statement, public instance, or other module was changed.
2. PASS: independently compiled the delivered file with lcompile.py without errors
   or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.existsUnique_dualNumberScheme_extension` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`. Scanned the entire file: no sorry,
   axiom, unsafe, opaque, implemented_by, or extern. The stalk maps are obtained from
   proved Mathlib correspondences, and the extension ring map is explicitly constructed;
   no arbitrary witness is chosen from an unproved existence theorem.
3. PASS: no statement was split off and no new public statement or node was added.
   Checked all four private helpers: locality is the unit criterion; residue and
   projection maps reflect units; localSpec_injective is injectivity of the inverse
   local-spectrum equivalence at a fixed point. These hold over every field and in
   arbitrary characteristic. For n = 1 the single projection determines both
   coefficients; n = 2 is the usual pushout; n = 0 is correctly excluded by hn.
4. PASS: read the proof top down, including coefficient multiplication, locality of
   the assembled ring map, projection equalities and uniqueness. Independent LeanFinder
   search for gluing infinitesimal spectra with identical residue maps found no direct
   theorem; Loogle confirmed the square-zero unit criterion; rg on both library roots
   and pinned Mathlib found no shorter gluing proof. Upstream
   WeilConjectures.Mathlib.RingTheory.DualNumber does already provide locality and
   residue-locality instances. The private helpers prove those elementary facts in
   a few lines without another module dependency; no replacement is required.
   All statement imports remain needed, and Stalk is correctly a plain proof import.
   Both original proof dependencies are used, so No longer needed is complete.
   Read dag/units/sk-thm-picard-rr.json: its realized statement and step lists are
   currently empty; this delivery leaves them intact and follows the node's existing
   tangent-vector pushout route without bypassing a unit.
5. PASS: read lem-sc-dual-number-scheme-pushout and both dependency nodes. Its three
   proof steps exactly describe the implemented coefficient construction and the
   Stalk correspondence for existence and uniqueness. proof_deps remains
   def-sc-dual-numbers and lem-weil-pbc-morphism-from-spec-local-ring, and the
   document-based proof_origin remains appropriate. No node repair is needed.

Second reading changed only this report: added the independent checks and verdicts.
The Lean proof and DAG were left as reviewed. One original hole is closed and zero
holes are added; none are split off or pruned.
