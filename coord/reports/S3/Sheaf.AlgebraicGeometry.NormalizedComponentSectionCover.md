## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_normalized_component_section_cover`
in `Sheaf.AlgebraicGeometry.NormalizedComponentSectionCover` without changing its signature.
The proof follows Stacks Project tag 09NE, direct proof and final paragraph
(https://stacks.math.columbia.edu/tag/09NE), using the existing reduced-cover section theorem
and nonvanishing/local-generation equivalence.

The construction isolates every point of the intersection locus and removes the closed images
of the complements of the prescribed sections' generating loci. Outside the intersection locus,
it chooses a local component frame and extends its open to the ambient scheme by removing the
closed image of the complement. The reduced-cover bijection supplies the ambient coefficient.
The cover is indexed by the disjoint sum of the points in the intersection locus and its
complement, lifted into universe `max u v`. Distinct overlaps avoid the intersection locus.
A proved private helper `freeGenerator_empty` handles all empty component preimages using
the existing locality theorem with the empty covering sieve. There are no new public declarations, definitions, or statements.

Added the proof-only import `Mathlib.Topology.DiscreteSubset` for finite unions of closed
discrete subsets and isolating neighborhoods. Updated the existing DAG node's proof and
proof dependencies to reflect the explicit construction and use of the existing generating-locus
API. No blueprint unit statement or step is bypassed: this node is below the unit level.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.Modules.exists_normalized_component_section_cover`
(node `lem-sc-normalized-component-section-cover`). Added zero holes; split off zero statements.
There are no `sorry`s left in the delivered module or added elsewhere.
The helper `freeGenerator_empty` is proved as well.

Local compilation passes without warnings. A separate sandbox check prints the theorem's
axioms: exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
All original hypotheses, universes,
conclusions and public imports are preserved. The construction treats empty schemes, empty
intersection loci, empty component preimages, and empty index types without special assumptions.

## No longer needed

Removed the redundant proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`; its definitions are already available
through the preserved public imports, and the proof uses the local-generator API available
through the remaining dependencies. This does not prune its definition node
`def-sc-invertible-module`, which is still needed by the statement and proof.

No planned dependency node or module is mathematically eliminated. Both
`Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections` and
`Sheaf.AlgebraicGeometry.NonvanishingGeneratingLocus` are used. All five original proof
dependency nodes remain; `def-sc-section-generating-locus` is additionally recorded for the
existing generating-locus construction. No new module is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error or unusable dependency was found. The DAG's component-open
indexing is simplified to one chosen neighborhood per point off the intersection locus.
The locally absent `literature/stacks-project/varieties.tex` was read through the official
Stacks Project tag 09NE page instead. The source's argument is retained.

## Second reading by S3

1. PASS: compared the sole delivered module with the repository using `diff` and a
   byte comparison of the existing theorem signature. Its hypotheses, universes,
   conclusion, visibility and public imports are unchanged. There are no definition
   changes, other delivered modules, or change records.
2. PASS: independently compiled the module with `lcompile.py` without errors or
   warnings, and checked its theorem with `#print axioms` in a scratch copy: only
   `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, forbidden declaration,
   hollow definition, or data from an unproved existence theorem is introduced.
   The chosen neighborhoods and frames come from proved locality/existence results;
   the ambient coefficients come from the proved structure-section bijection.
3. PASS: no statements or holes are split off. Read the private empty-open helper
   and checked the empty scheme, empty intersection locus, empty component preimage,
   empty index, single component and repeated component cases. Repeated components
   cause no failure: their common locus belongs to T and is discrete by hypothesis.
   Searched the upstream library and Sheaf for alternative frame-cover and empty-open
   generator lemmas, and ran an independent Loogle search for `IsFreeGenerator`.
4. PASS: the proof uses the existing reduced-cover and nonvanishing-generation
   theorems, Mathlib's discrete-union/isolation API, and upstream frame locality.
   No shorter whole-theorem replacement was found. All original proof dependency
   nodes remain used; the removed explicit Invertible import is transitively present.
   Read `dag/units/sk-thm-curveestimate.json`: this node is not one of its realized
   statements or steps, and the unit route stays intact. No module is pruned.
5. PASS: the node changes only `proof` and `proof_deps`; their steps describe the
   actual construction and the dependency list is exactly the union of their uses.
   The retained document proof origin agrees with the direct proof and normalization
   paragraph of [Stacks tag 09NE](https://stacks.math.columbia.edu/tag/09NE), read
   independently. The existing generating-locus dependency accounts for that API.

Changed the private empty-open helper's proof from a direct separatedness argument
 to the existing `isFreeGenerator_of_mem` applied to the empty covering sieve, matching
 the short proof of upstream `isFreeGenerator_bot` without importing its unrelated
 projective-space module. Updated the report accordingly. Kept the main proof and all
 signatures. One original hole closed, zero holes added; no decomposition.
