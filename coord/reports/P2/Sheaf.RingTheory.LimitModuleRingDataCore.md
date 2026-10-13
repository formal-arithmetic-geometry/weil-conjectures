## What changed

Proved `RingHom.exists_limit_module_ring_data_core` with its entire signature unchanged.
Added two proved supporting modules:
`Sheaf.RingTheory.FiniteTypeRingSystem` constructs polynomial-image subrings over the
original stages, and `Sheaf.RingTheory.LocalizeFilteredRingSystem` localizes a filtered
ring diagram using the existing `filteredColimitLocalizationAtPrime` theorem.
All new imports in the existing module are private proof imports. The second reader
also made the localization helper's LocalRing.RingHom.Basic import private, exporting
only LocalRing.Defs and Algebra.Group.Units.Hom for its local-ring and local-map types. No existing definition,
statement, visibility, or public import was changed; no other existing module was adapted.
The core DAG proof now records the finite-generator route and these two dependencies.

The complete three-module set compiles with lcompile.py, in approximately four seconds
per file, with no warnings. `#print axioms` for all three public theorems reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the one original hole in `RingHom.exists_limit_module_ring_data_core`
(node `lem-weil-pbc-limit-module-ring-data-core`). Added zero holes and split off zero
unproved statements. Both new theorems are fully proved:
`RingHom.exists_finiteType_ring_system` and
`RingHom.exists_localized_filtered_ring_system`. No sorry remains in any delivered file,
and the axiom audit confirms that these declarations do not depend on sorry elsewhere.
This is one proof, not a decomposition into additional holes.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime` from the core module;
it remains used transitively by `Sheaf.RingTheory.LocalizeFilteredRingSystem`.
No existing module or DAG node is pruned from the transitive import closure.
The old node had no named proof dependencies, so no dependency node can be listed as
removed. Descending presentation relations and choosing finite presentations of stage
rings are unnecessary for this core statement: it asks only for essentially finite type
structure maps. The finite-presentation hypothesis is used to obtain finite type and
smallness; the original local-transition hypothesis `hF` is retained but unnecessary.

## Where the brief, the DAG or earlier work was wrong

The earlier plan was stronger than necessary, rather than false: it descended the whole
finite presentation, whereas polynomial images already give the requested finite type
stages. The stated theorem and all five targets remain unchanged. The unit route is kept:
this auxiliary core node is not a unit statement or a realized unit step, and the new
argument proves the same auxiliary assertion below that level.

The source was read at the official Stacks Project pages for
[00QV](https://stacks.math.columbia.edu/tag/00QV) and
[037D](https://stacks.math.columbia.edu/tag/037D); the local literature files were absent.
The polynomial-image variant is an agent-written proof of the finite type conclusion.
The LeanSearch service returned Internal Server Error, recorded as unavailable;
LeanFinder, Loogle, and source grep were used successfully.

Edge cases checked in the construction: empty generator sets, noninjective base maps,
non-antisymmetric directed preorders, distinct universes for P and the base, and a
one-object system. The finite type system also allows the zero ring. The localization
lemma retains the nontrivial local-target condition; it never silently treats the zero
ring as local. All stages and maps are explicit constructions from generators or
canonical localizations, with no data chosen from an unproved existence theorem.

An initial subalgebra representation exceeded the kernel-check limit through conversion
between inherited ring structures. Replacing it by polynomial-image subrings with named
diagram and cocone constructors reduced the successful compile to four seconds without
raising any limit or splitting a slow file into separate files.

## New nodes

`lem-weil-pbc-finite-type-ring-system` records the proved finite-generator construction
in `Sheaf.RingTheory.FiniteTypeRingSystem`. Its statement only promises finite type,
so it is strictly the unlocalized part needed here and requires no presentation descent.
The proof identifies the ring colimit by representatives, inclusion in a common stage,
and bijectivity of the induced map. Searches found the elementary ingredients, but
no existing theorem supplying this compatible stage system.

`lem-weil-pbc-localize-filtered-ring-system` records the proved localization construction
in `Sheaf.RingTheory.LocalizeFilteredRingSystem`. It applies the existing prime-localization
colimit theorem, enlarges denominators using `IsLocalization.of_le`, and transports the
cocone along the unique localization algebra equivalence. Its proof dependency on
`lem-weil-pbc-filtered-colimit-localization-at-prime` is preserved. Both new nodes inherit
the core node's chapter, unit, and blueprint ancestry. No change record is needed.

## Second reading by P2

1. PASS: Compared the core module and its existing node against the repository with
   diff. Programmatically checked the entire existing theorem signature byte for byte;
   it is unchanged, including all hypotheses and all conclusion clauses. The original
   module has no definitions to alter. The two other modules and nodes are genuinely
   new. Existing-node edits are confined to proof, proof_deps and proof_origin; there
   are no statement or definition changes and no forced adaptations. The core docstring
   was updated by the first worker to describe the actual route.
2. PASS: Independently compiled all three delivered files through lcompile.py in import
   order, with no errors or warnings, then recompiled after the import repair. Searched
   all delivered Lean sources for forbidden declarations and sorry: none occur.
   A scratch copy with explicit #print axioms for all three public theorems compiled;
   each reports exactly propext, Classical.choice and Quot.sound. In particular the
   imported localization theorem contributes no sorryAx. stageDiagram and stageCocone
   construct real subring inclusions, and no object is chosen from an unproved theorem.
3. PASS: There are zero split-off unproved statements. Read both proved helpers and
   their complete docstring arguments. Checked the empty-generator case (constants
   still cover the base image), the zero finite-type algebra, noninjective coefficient
   maps, one-object systems and directed preorders without antisymmetry. The localization
   argument requires a nontrivial local T and contracts its maximal ideal to a prime;
   it makes no zero-ring locality claim. The arbitrary initial tail index is selected
   from a genuine Nonempty instance, and finite generators from the proved finite-type
   property. Independent searches used Loogle with RingHom.range, RingHom.FiniteType,
   LeanFinder with compatible subrings over directed coefficient rings, and LeanFinder
   with localization at inverse images of a maximal ideal. Results concern morphism
   factorization or concrete filtered colimits, not either complete helper. Source grep
   in lean/ found the existing prime-localization colimit theorem and related away
   localization systems; the helper correctly reuses that existing theorem. Verified
   the cited constructions on the official Stacks pages for 00QV and 037D.
4. PASS after import repair: The finite-type conclusion needs no descent of relations;
   polynomial images and a common-stage equality argument provide the shorter route.
   The localization step reuses the existing proved library theorem. Read sk-thm-p1's
   realized statement and steps: this auxiliary core is absent from those lists, and
   no realized unit step is bypassed or changed. The old core proof_deps is empty.
   No old dependency node or transitively reachable module is pruned; the old direct
   localization import is still reached through the new helper. Corrected the new
   helper's proof-only public import as described below.
5. PASS: Checked every node's verbatim lean.statement against its theorem signature
   and proof_deps against the union of the proof steps' uses. Read each proof and
   proof_origin against the Lean implementation. New nodes include sources, searches,
   created records, blueprint ancestry, chapter, unit and complete lean records.

Second-reading changes: In LocalizeFilteredRingSystem, changed
Mathlib.RingTheory.LocalRing.RingHom.Basic from public import to proof-only import;
added public imports of Mathlib.RingTheory.LocalRing.Defs and
Mathlib.Algebra.Group.Units.Hom, which supply the types occurring in the statement.
No proof or statement needed repair. Updated this report and performed fresh compilation
and the explicit axiom audit. Holes closed remain one; holes added remain zero.
