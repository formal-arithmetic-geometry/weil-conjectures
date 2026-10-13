## What changed

Proved AlgebraicGeometry.isUniversalFirstOrderThickening_of_affine_local with its
signature unchanged. Added three fully proved private helpers in the same module:
firstOrderThickening_pullback_open (canonical open pullback),
unique_lifts_of_affine_tests, and lifts_of_affine_tests (both affine test schemes).
The argument adapts the already proved private helpers in
Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase; these are inaccessible to
importers, and no other module is changed. The new versions use distinct signatures:
canonical pullback rather than a supplied square, and both test schemes affine.
Removed the unused public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified.
Updated the node's proof, proof_deps and proof_origin to the actual route.

The three requested searches ran through msearch.py: LeanFinder for affine-test
unique lifting globalization (no exact match); Loogle for IsAffineHom and IsAffine
(found isAffine_of_isAffineHom); grep for lifts_of_affine_tests and
isAffine_of_isAffineHom. Direct project search found the private existing gluing
proof. Compiled the initial adaptation, the pruned version, and the final helpers
using lcompile.py, with no warnings or errors.

## Proved and sorry left

Closed 1 hole: AlgebraicGeometry.isUniversalFirstOrderThickening_of_affine_local
(node lem-weil-pbc-universal-first-order-thickening-globalization).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
All three private helpers have complete proofs. The delivery axiom probe is checked
by deliver3.py. No definitions, existing signatures or target statements change.

## No longer needed

Removed import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified: neither the
statement nor its proof needs formal unramifiedness.
Removed proof dependency lem-weil-pbc-universal-thickening-open-pieces, whose module
Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces is not imported. Its full
universal-thickening restriction and base-enlargement theorem is unnecessary;
open pullback square-zero preservation is proved directly from Mathlib's kernel
formula. No other planned dependency is pruned. The replacement dependencies are the
Mathlib leaves lem-weil-pbc-affine-opens-basis and lem-weil-pbc-scheme-morphism-gluing.
This is pruning from this proof, not a claim that no other target needs those modules.

## Where the brief, the DAG or earlier work was wrong

The original DAG cited the much larger open-pieces theorem for test globalization.
Only preservation of square-zero kernels under open pullback is needed here.
The local sources must be shown affine to use the two-affine-test hypothesis;
closed immersions being affine supplies this without any extra assumption.
Overlap targets need not be affine: first prove global uniqueness by affine covers,
then apply it on the overlaps. This handles nonseparated and empty schemes and
does not assume a finite cover. The item is not a realized statement or step of
sk-thm-p1, and no unit route changes.

The local literature checkout lacks more-morphisms.tex. Read the official Stacks
More on Morphisms PDF, Tag 04F3, page 14, the affine-test gluing paragraph:
https://stacks.math.columbia.edu/download/more-morphisms.pdf . It explicitly glues
by agreement on affine opens of overlaps, which is what the global uniqueness
helper formalizes. No new unproved statement or source-dependent hole was added.

Change record: coord/changes/universal-first-order-thickening-globalization-import.md.
The sole direct importer already publicly imports the removed Mathlib module, so
no downstream adaptation is needed; the import-pruning check passed.


## Second reading by W4

1. PASS: compared the sole delivered module with the repository using diff and
   checked the existing theorem signature byte for byte with a script. The only
   existing declaration changes its proof; no definition or target changes.
   The removed public import has the supplied change record. The sole direct
   importer explicitly publicly imports FormallyUnramified itself, so pruning
   does not remove any downstream availability. No adapted module is delivered.
2. PASS: independently compiled the module with lcompile.py, without errors or
   warnings. Scanned its complete source: no sorry or forbidden declaration or
   attribute. In a scratch copy, #print axioms on the public theorem and all three
   private helpers reports exactly propext, Classical.choice, and Quot.sound.
   Local choices are of lifts established by proved unique-existence arguments;
   there is no data construction from an unproved existence theorem.
3. PASS: no split-off statement, new module, new node, or added hole. Read the
   private helper statements and proofs: open pullback preserves closedness and
   square-zero kernels; a closed immersion into an affine scheme has affine
   source; equality is local on an affine cover. Empty schemes and zero kernel
   cause no exception. Overlaps are allowed to be nonaffine and no finiteness or
   separatedness hypothesis is silently used.
4. PASS: checked the shortest-route issue by an independent LeanFinder query
   about square-zero extension on affine open covers, and searched project and
   Mathlib sources for infinitesimal lifting/globalization interfaces. No public
   theorem directly supplies this project-specific lifting predicate. The similar
   upstream project helpers are private and their affine-test hypothesis differs;
   the present adaptation is justified. The single remaining import is required
   by the public signature. Checked all original proof_deps: the sole old
   dependency, lem-weil-pbc-universal-thickening-open-pieces, is explicitly listed
   as unused. Checked sk-thm-p1's realized statement and steps: this item is not
   a realized node; the unit route is preserved. Gluing is justified by global
   uniqueness before existence, including on nonaffine overlaps.
5. PASS: compared the delivered node with its repository version. Only proof,
   proof_deps, and proof_origin differ. Read the two replacement Mathlib leaf
   records; affine covers, hom_ext, and glueMorphisms implement their roles.
   The three proof steps match the three private helpers and final packaging.
   Source, statement, Lean signature record, and unit are unchanged.

Second-reading changes: corrected “retained dependencies” to “replacement
dependencies” in the pruning report, since the two Mathlib leaves replace the
original dependency. Added this independent review. No Lean or node repair was
needed. Confirmed holes closed: 
AlgebraicGeometry.isUniversalFirstOrderThickening_of_affine_local (1 of 1); holes added: none.
