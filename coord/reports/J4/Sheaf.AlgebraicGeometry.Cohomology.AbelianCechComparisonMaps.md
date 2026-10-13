## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.Modules.exists_abelianCechComparison_maps`
now follows from two strictly smaller public theorems in new modules. Classical choice
assembles the comparisons supplied degree by degree by `AbelianCechComparisonCore`; the
separate `AbelianCechComparisonNormalization` theorem uses only the degree-zero equation
to give the required value. Both imports are proof-only. No existing signature,
definition or visibility changed. The original node now records this reduction.

The two new modules have complete source-labelled proof descriptions and matching DAG
nodes with verbatim Lean signatures. All three modules compile through lcompile.py
against the shared baseline, after removing stale sandbox build outputs.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.exists_abelianCechComparison_maps` (the single
original hole), by a complete Lean reduction.

Added and left: `AlgebraicGeometry.Scheme.Modules.exists_abelianCechComparison_core`
(node `new-abelian-cech-comparison-core`) and
`AlgebraicGeometry.Scheme.Modules.abelianCechComparison_zero_normalization`
(node `new-abelian-cech-comparison-normalization`). Each is exactly `:= by sorry`.
There are no other holes in the delivered files. This is a decomposition, not a
sorry-free proof: one upper hole closed, two lower holes added (net minus one).

## No longer needed

No imports, dependency nodes or library modules were pruned. The old direct
proof dependencies `def-pc-abelian-cech-comparison-construction` and
`lem-pc-topological-cech-zero-gluing-iso` now occur below the split nodes;
they are retained transitively, rather than discarded. The construction and
zero-gluing nodes remain needed by the split statements. Forty unchanged dependency
copies and stale probes were removed from the sandbox delivery set; these are not
library pruning. Only the assigned module and the two new modules are delivered.

## Where the brief, the DAG or earlier work was wrong

The retained attempt compiled a large collection of unchanged dependency copies.
Those copies are unnecessary when compiling against the supplied shared build and
are outside the changed-file delivery set. The retained new nodes also had placeholder
Lean signatures, inherited review claims and vague proofs; these have been replaced
with verbatim signatures, fresh search records and explicit stepwise arguments.

The new core statement concerns one degree and requires no covering hypothesis.
The normalization statement concerns a single degree-zero map, without a comparison
family or a quasi-isomorphism hypothesis. In degree zero the homology projections are
invertible because no boundaries enter degree zero; this is why the weaker hypotheses
suffice. Empty-space/empty-cover, zero-coefficient and infinite-cover cases were checked
in the proof descriptions. The unit record has no realized nodes here; the original
construction-and-normalization route remains intact.

Searches: LeanFinder found the sheaf cohomology definitions and the Ext cocycle
computation, but no exact comparison theorem. Loogle returned `extMk_surjective`,
`extMk_comp_mk₀` and related Ext formulas. The wrapper grep found no exact match;
direct rg found the existing predicate and source degree-zero gluing theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable.
The source read was Stacks Tag 01EQ; its final functoriality verification is omitted,
and the new core docstring spells out the resolution-lift argument required here.

## New nodes

`new-abelian-cech-comparison-core`: existence of the quotient in one fixed degree,
without normalization or a cover hypothesis. Module `AbelianCechComparisonCore`.

`new-abelian-cech-comparison-normalization`: the canonical zero value forced by the
zero-degree quotient equation alone. Module `AbelianCechComparisonNormalization`.

No change records or forced adaptations are needed.


## Second reading by J4

1. Checked the diff of AbelianCechComparisonMaps against the repository: its
   theorem signature and visibility are byte-for-byte unchanged, as is its
   docstring. The only code changes are two plain proof imports and the proof.
   There are no definition or existing-statement changes and no change records.
   Verdict: unchanged interface.

2. Compiled all three delivered modules locally in import order (2.6, 2.2 and
   2.4 seconds). A scratch copy printed axioms for all three public theorems:
   exactly propext, Classical.choice, Quot.sound and sorryAx. The scratch copy
   was removed. Inspected all files for forbidden declarations and hidden holes:
   the two named public theorems are the only sorries, each exactly `by sorry`.
   Choice in the main proof only proves an existential proposition; no data
   definition chooses an arbitrary witness. Verdict: valid reduction, with two
   explicitly open mathematical statements, not a completed axiomatic proof.

3. Read the core and normalization signatures, docstrings and node statements
   against the explicit IsAbelianCechComparison predicate and Stacks Tag 01EQ
   (https://stacks.math.columbia.edu/tag/01EQ). The source constructs beta followed
   by inverse alpha and omits functoriality; the core docstring supplies the
   resolution-lift squares and Ext cocycle compatibility. Core fixes one degree,
   requires hα, and neither assumes a cover nor asserts normalization. The
   normalization lemma assumes a cover and the degree-zero predicate, and uses
   no positive-degree map or quasi-isomorphism. These are strictly separate parts
   of the original conclusion, not a renamed copy of that conclusion.
   Checked zero coefficients, degree zero, empty space, empty index set and
   infinite covers: no division, finite-cover assumption or excluded zero case.
   For non-covering families the core uses only the supplied hα. An empty cover
   in normalization forces an empty space. The degree-zero argument uses the
   absence of incoming boundaries, the (0,0) component, separatedness and the
   kernel property of the augmented resolution. Clarified the last kernel step:
   a factors uniquely through I.ι.f 0, and Ext-zero identifies its class with
   Ext.mk₀ of that factor. Verdict: both statements are true and needed.
   Independent searches used new wording through LeanFinder, Loogle and grep;
   direct rg covered both library roots. resolution_section_cohomology gives a
   Nonempty isomorphism with object cohomology on an integer complex, without
   this explicit augmentation equation. The small-etale extSectionsIso is for
   another site and a chosen resolution. Neither replaces these statements;
   cechCohomologyZeroIso supplies exactly the gluing already used here.

4. Read the main proof downward: choice assembles the single-degree comparisons;
   normalization applied to hc 0 supplies the last conjunct. Both new imports
   are necessary and proof-only. Construction is public because it occurs in
   every signature. The old construction and zero-gluing dependencies remain
   transitively needed; none was pruned. Read sk-thm-picard-rr.json: its realized
   statement list and step list here are empty; no realized node is bypassed.
   No short existing lemma closes either lower statement, which each requires
   a complex/resolution comparison. Verdict: route preserved; decomposition,
   one original hole closed and two added, net minus one.

5. Parsed and compared the existing node against its repository version: only
   proof, proof_deps and proof_origin differ. Both new nodes have the required
   source, creation, blueprint, chapter/unit, searches and Lean records. Every
   Lean statement record is verbatim. The original proof_deps is exactly the
   union of the two proof steps, and the split nodes retain construction and
   gluing where used. Verdict: records agree with the delivered reduction.

Changes from this reading: expanded the normalization docstring and its node's
final proof step to spell out the unique degree-zero factorization and Ext.mk₀
identification; recorded independent searches in both new nodes; clarified the
retained old dependencies in No longer needed; added this review. No Lean proof,
statement, definition, visibility or import changed during the second reading.
