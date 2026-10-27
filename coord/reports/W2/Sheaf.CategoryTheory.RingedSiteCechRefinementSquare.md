## What changed

Corrected `CategoryTheory.ringedSite_cech_refinement_square_rest` by restoring the tuple-formula
hypothesis on gamma, already required by its natural-language DAG statement and Stacks 01FD.
Its sole caller now passes the formula it already proves. Both the parent refinement-square
signature and the abelian specialization signature stay identical.

Proved the corrected auxiliary theorem from three strictly smaller components. The proof applies
homology to the actual pentagon, proves invertibility of its middle arrow from its lower square,
and cancels to establish the refinement square. It proves the nested uniqueness clauses by
normalized-edge uniqueness and cancellation of one replacement roof. No partially admitted
proof remains in the item module.

Added `RingedSiteNormalizedCechEdge`, with a complete proof of existence and uniqueness for
arbitrary coefficients. Its proved private restriction, augmentation and comparison helpers
reuse the construction in `AcyclicCechEdgeCompatibility`; those helpers are private there,
and its public theorems require acyclic coefficients. The new theorem needs neither coefficient
acyclicity nor terminality. All constructions are explicit; no data definition uses a hole.

Added two separate smaller proof tasks: `RingedSiteResolutionRoof` contains only the direct-image
roof and its all-resolution normalization, with no covering data; `RingedSiteCechRefinementPentagon`
contains the actual chain-level pentagon and augmentation squares, with no derived edge,
resolution independence, or uniqueness assertion. Each has its source and complete proof in
words. Their statements were checked on identity refinements, degree zero, zero coefficients,
and empty covering families; they require no hidden coefficient acyclicity.

Change record: `coord/changes/W2-ringed-site-refinement-tuple-hypothesis.md`.
Only the sandbox is edited. Compilation uses lcompile.py throughout.

## Proved and sorry left

Original item: one sorry, in `CategoryTheory.ringedSite_cech_refinement_square_rest`.
That original statement was false, so its removal is not claimed as a proof of the old statement.
The corrected statement is fully reduced to the following two named holes; this is a
decomposition, not a net hole closure. The item module itself has zero sorry.

Proved: `CategoryTheory.ringedSite_normalized_cech_edge`
(node `lem-weil-pbc-ringed-site-normalized-cech-edge`), including all its private helpers;
the corrected `CategoryTheory.ringedSite_cech_refinement_square_rest` combining the components;
and the existing `CategoryTheory.ringedSite_cech_refinement_square` caller still compiles.
The existing proved abelian specialization is preserved.

Holes added and remaining:
- `CategoryTheory.ringedSite_resolution_roof`
  (`lem-weil-pbc-ringed-site-resolution-roof`).
- `CategoryTheory.ringedSite_cech_refinement_pentagon`
  (`lem-weil-pbc-ringed-site-cech-refinement-pentagon`).

Counts: one original hole replaced after statement repair, two new holes, one new component
proved completely; net hole change +1. No axioms or admitted definitions are introduced.

## No longer needed

No existing public import or existing declaration was removed. No module is withdrawn.
The parent node no longer directly carries the lower proof dependencies:
`def-weil-pbc-sites-and-cohomology`, `def-weil-sheaf-of-modules-category`,
`def-sp-injective-resolutions`, `lem-weil-pbc-complex-injective-resolution-mono`,
`lem-weil-pbc-lift-along-injective-quasi-iso`,
`lem-weil-pbc-ringed-site-injective-module-cech-acyclic`,
`lem-sc-first-quadrant-column-augmentation`, `def-sp-double-complex-total`,
`lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic`,
`lem-weil-pbc-derived-functor-injective-vanishing`,
`lem-weil-pbc-leray-acyclicity-quasi-iso`, and
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`.
Their mathematics remains needed inside the three component nodes, with explicit proof steps.
This is dependency organization, not pruning those modules out of the target closure.
The rest node now uses the three component nodes and edge normalization. The parent uses
its tuple-map construction, the repaired rest node, and the existing abelian existence node.
The unit statement and its realized steps are untouched.

The normalized-edge module omits PullbackContinuous, Pullback and PushforwardContinuous
and keeps its proof dependencies as private imports. Roof and pentagon retain
PullbackContinuous because its module-pushforward instances are needed in their signatures.
No target-reachable module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The auxiliary Lean statement omitted gamma's tuple formula even though its DAG statement
explicitly fixes gamma by that formula. This was already marked STATEMENT-DISPUTED in the
source. On the terminal identity site with singleton identity cover, constant integer modules,
h the identity and gamma zero, the old degree-zero square would say identity equals zero.
The correction adds exactly the missing source requirement. Searching both Lean roots and
running downstream.py --uses finds one declaration user, in the same module; it already has
the required formula. No target or public parent signature changes.

The previous rest proof step merely restated its whole assertion and cited definitions.
It is replaced by three mathematical components and an explicit Lean diagram chase.
The existing AcyclicCechEdgeCompatibility public edge results are not arbitrary-coefficient
existence results, despite having much of the needed construction privately. Its construction
is reused in a proved new component rather than adding an acyclicity assumption.

## New nodes

`lem-weil-pbc-ringed-site-normalized-cech-edge`: normalized edge existence and uniqueness for
arbitrary module coefficients, proved from injective Cech vanishing and first-quadrant
augmentation, with strict-resolution naturality. LeanFinder, Loogle, Mathlib grep and LeanSearch
were run; the local library was searched for IsNormalizedEdge and Augmentations.

`lem-weil-pbc-ringed-site-resolution-roof`: direct-image resolution roof and its normalization
for every source/target resolution and every injective replacement, with no Cech data.
The node records the strict comparison and homotopy-independence argument.

`lem-weil-pbc-ringed-site-cech-refinement-pentagon`: the actual Cech-first chain total diagram,
its two quasi-isomorphic restriction augmentations and five chain equalities. The node records
the tuple maps, strict coefficient identity, image covering row argument and sign convention.

All three nodes inherit the item's chapter and unit; both existing nodes record the proof
actually written. Change record: `coord/changes/W2-ringed-site-refinement-tuple-hypothesis.md`.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
