## What changed

Replaced the single sorry in
`AlgebraicGeometry.Scheme.Modules.orderedCech_module_comparison` by a complete Lean
argument from a split retraction and null-homotopy of its ordered kernel. The
original signature and all its public imports are unchanged. Added proof-only
imports of `OrderedCechModuleRetraction` and
`OrderedCechModuleKernelNullHomotopic`.

Added `OrderedCechModuleCoordinates` with actual maps from increasing
intersections to chosen categorical products and an actual ordered-coordinate
function for the pushed-forward, extended usual presentation. Proved
`orderedCechTupleOpenMap_isIso`, `orderedCechModuleCoordinate_add`,
`orderedCechModuleCoordinate_zero`, `orderedCechModuleCoordinate_smul` and
`orderedCechModuleCoordinate_naturality`. All coordinate data is explicitly
constructed; no witness of a postponed existence theorem is used in a definition.

The main proof obtains the two cochain maps inside a proof, sets
`g = rmap ≫ imap - 𝟙`, proves `g ≫ rmap = 0`, evaluates that identity on sections,
and uses the coordinate formula to prove that every ordered coordinate of g is
zero. The kernel lemma then gives one homotopy; the exact retraction identity
gives the other. Updated the original DAG proof to that argument. No statement,
definition, existing visibility or other module was changed.

Validation: all four modules compile in sandbox import order, including the
coordinate properties and complete main proof. The delivery dry run is the final
validation. No target, unit statement or unit proof route is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.orderedCech_module_comparison`
(node `lem-pc-ordered-cech-module-comparison`). Its proof contains no sorry.

Added exactly two named theorem holes, each with source and complete proof in
words in its own module and matching node:

- `AlgebraicGeometry.Scheme.Modules.orderedCech_module_retraction`
  (`lem-pc-ordered-cech-module-retraction`,
  `Sheaf.AlgebraicGeometry.OrderedCechModuleRetraction`). It proves only the
  cochain retraction and coordinate formula, with no homotopy conclusion.
- `AlgebraicGeometry.Scheme.Modules.orderedCech_module_kernel_nullHomotopic`
  (`lem-pc-ordered-cech-module-kernel-null-homotopic`,
  `Sheaf.AlgebraicGeometry.OrderedCechModuleKernelNullHomotopic`). It proves
  null-homotopy of an arbitrary endomorphism with vanishing increasing
  coordinates and has no ordered complex K or its identification a as input.

This is a decomposition: one hole closed, two added, net minus one hole. It is
not a proof free of postponed dependencies. `OrderedCechModuleCoordinates`
contains no sorry. The original module contains no remaining sorry.

Checked empty index families, empty opens, repeated cover members, degree zero,
negative degrees and degrees p+1>r against the two new statements. The retraction
uses empty products in the empty-family case; the kernel statement has its
vanishing condition in every degree, with sorting contractions still applying
in degrees with no increasing tuples. No cover, affine or flatness assumption
is used.

## No longer needed

No original import, node or module was pruned. Both original definition nodes
remain necessary to state the theorem. Removed an unnecessary draft import of
`Mathlib.Algebra.Homology.Homotopy` from the new retraction module.

The new retraction node uses `lem-pc-signed-cech-extension-differential` as a
combinatorial tool. The new kernel node uses
`lem-pc-alternating-cech-first-sorting-identity` and
`lem-pc-alternating-cech-second-sorting-identity` as combinatorial tools.
These are reusable additive cochain results from the projective-space unit;
they do not replace that unit's route or the coherence unit's argument.
The maintainer may record those generic tool uses when reviewing the new nodes.

## Where the brief, the DAG or earlier work was wrong

The original proof describes sorting maps and homotopies without naming their
module-sheaf assembly statements. Existing additive cochain comparison lemmas
supply no local scalar or restriction-compatibility conclusion, so simply
choosing their existential maps or homotopies would not justify the requested
module-sheaf maps. The new nodes state the two missing assembly obligations
separately and include explicit local scalar hypotheses inherited unchanged
from the original statement.

Mathlib searches found generic HomotopyEquiv and Dold-Kan results, but no
matching ordered module-sheaf comparison. LeanSearch returned Internal Server
Error; the recorded semantic, type and local source searches were usable.
The literature checkout on this machine contains lists but not cohomology.tex;
read Stacks Tags 01FJ, 01FK and 01FM directly. Their formulas do not use the
covering assertion, so the arbitrary-open-family formulation is appropriate.
The source omits the sorting identity verifications; their existing DAG
nodes, rather than an unsupported claim of automatic cancellation, remain the
combinatorial prerequisites.

## New nodes

`def-pc-ordered-cech-module-coordinates` records explicit intersection/product
transport and ordered evaluation of the usual presentation; its module also
proves the transport isomorphism, additivity, zero, local scalar law and
naturality. There is no postponed data or proof in that module.

`lem-pc-ordered-cech-module-retraction` records restriction and signed extension
as cochain maps whose ordered composite is identity, together with the exact
coordinate formula used in the main Lean proof. It contains no usual-complex
homotopy and is strictly part of the comparison argument.

`lem-pc-ordered-cech-module-kernel-null-homotopic` records the sorting contraction
for an endomorphism with zero ordered coordinates, independent of K and a. Its
proof uses the two existing sorting identity nodes and explicitly explains
restriction, local linearity and extension to integer degrees.

No change record is required: every existing statement and definition is
unchanged; no forced adaptations occurred.

## Second reading by K2

1. Compared the existing comparison module with the repository by diff. The
   original declaration, all hypotheses, conclusion, visibility, and docstring
   are byte for byte unchanged. The only additions are two plain proof imports
   and the proof body. The other three modules and nodes are new; no existing
   definition or interface was edited. Verdict: pass.
2. Compiled all four modules in import order using lcompile.py. Inspected every
   definition and proof and scanned for forbidden declarations. Exactly the two
   reported public named theorems contain `:= by sorry`. A scratch-copy
   `#print axioms` check on the comparison, both split statements, the coordinate
   definition and all five coordinate properties found only propext,
   Classical.choice, Quot.sound, and sorryAx for the comparison and the two
   postponed statements. The coordinate construction and its properties have
   no sorryAx. No data is chosen from an unproved existence theorem: the main
   proof eliminates existentials only to prove a proposition. Verdict: pass as
   a decomposition, not as a completed sorry-free comparison.
3. Read the two new statements and their complete docstring arguments against
   Stacks Tags [01FK](https://stacks.math.columbia.edu/tag/01FK) and
   [01FM](https://stacks.math.columbia.edu/tag/01FM). The first is a split cochain
   retraction with a coordinate formula and no homotopy; the second contracts
   arbitrary kernel endomorphisms and does not assume K or a. They are true,
   strictly smaller parts of the argument and neither restates the target.
   Checked r=0 (empty products and zero terms), r=1 (differentials on the full
   repeated tuple alternate zero and identity, with degree-zero kernel zero),
   repeated cover opens, empty coefficient opens, p+1>r, and negative and
   boundary degrees. No covering hypothesis enters the formulas. Repeated
   msearch.py searches with the different phrases "subcomplex of full Cech
   cochains with zero increasing coordinates is contractible",
   `HomotopyEquiv, Homotopy`, and the Cech/retract/homotopy grep pattern found
   generic complex tools but no module-sheaf assembly result. Read the existing
   additive AlternatingCechSection and AlternatingCechKernelNullHomotopic:
   their conclusions lack the naturality and local scalar equations required
   for module-sheaf maps. Neither new hole can be closed by a few-minute
   application of those results. Verdict: pass.
4. Checked the retraction identity, the computation g followed by rmap = 0,
   the sectionwise coordinate vanishing, and the orientation of both homotopies.
   The argument is a real reduction. Public imports in the new modules supply
   signature/definition types; the comparison's two added imports are plain.
   No old proof dependency is bypassed: its old two definition dependencies
   remain in the statement and its two public definition imports. No import,
   node or module was pruned. Read sk-thm-picard-coherence.json; its realized
   entries are currently empty, and this delivery alters neither that record
   nor its unit route. The sorting identities are generic tools, not a
   replacement for the coherence argument. Verdict: pass.
5. Compared all Lean signatures with their node records and checked the parent
   proof steps and dependency union. The retraction and kernel nodes describe
   their exact assembly obligations, sources and combinatorial prerequisites.
   New-node records have the required creation, source, search, blueprint,
   chapter, unit and Lean fields. Found the coordinate node's proof and
   proof_origin empty although its statement also records five proved
   properties. Completed those fields with the actual Lean construction and
   proofs. Verdict: pass after metadata repair.

Second reading changed only the coordinate node's proof and proof_origin and
this report. No Lean code or statement was changed. One original hole closed,
two strictly smaller holes added: net minus one, with no pruning.
