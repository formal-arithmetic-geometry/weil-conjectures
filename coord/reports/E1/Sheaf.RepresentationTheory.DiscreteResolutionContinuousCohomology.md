## What changed

Completed the retirement listed in coord/retire-items.tsv for
Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology.
The module's theorem was already proved; the existing upstream construction
Rep.invariantResolutionHomologyAddEquivContinuousCohomology is strictly stronger,
retaining the additive structure with identical hypotheses and universes.

Retired the local module using deleted.txt. Migrated its sole direct consumer,
Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison, by replacing its
private proof import with the upstream module and taking the construction's toEquiv.
The consumer's original public signature and visibility remain identical.
No source-library file is changed.

Reattached lem-sc-discrete-resolution-continuous-cohomology to the upstream
construction and clarified its final proof step. Updated the parent node's proof
step to name the construction and toEquiv. Mathematical statements, dependency
edges, and the sk-thm-br unit route are preserved.

Change record: coord/changes/E1-retire-discrete-resolution-continuous.md.

## Proved and sorry left

Holes closed: zero of zero. Holes added: zero. Split off: zero.
The retired Rep.nonempty_equiv_invariantResolution_continuousCohomology already had
no sorry. Rep.nonempty_equiv_rightDerived_continuousCohomology remains proved using
the existing upstream construction. No delivered Lean file contains sorry.

The original item compiled through lcompile.py in 2.3 seconds; the adapted consumer
compiled without warnings in 1.9 seconds. An explicit #print axioms check of the
upstream construction and the consumer theorem reports exactly propext,
Classical.choice, and Quot.sound (1.1-second compile). The delivery tool also checks
the delivered consumer with its axiom probe. A separate scratch check reproduced
the entire original theorem signature and proved it directly by taking the upstream
construction's toEquiv; it compiled in 1.6 seconds with only the three allowed axioms.

## No longer needed

Pruned Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology, including
Rep.nonempty_equiv_invariantResolution_continuousCohomology and its duplicated proof.
Removed its private proof import from DiscreteInvariantsContinuousComparison;
replaced it with WeilConjectures.RepresentationTheory.DiscreteResolutionContinuousCohomology.

The retired module's public imports of DiscreteContinuousRep, Invariants,
ContCohomology.Basic, RightDerived, and Grp.AB, and its private imports of
DiscreteResolutionInhomogeneousCohomology and
HomogeneousInhomogeneousContinuousCohomology disappear with this duplicate file.
These mathematical dependencies remain needed by the adopted-source construction;
none is claimed pruned from the library. All original DAG nodes and mathematical
dependency edges remain. The parent continues to use the reattached comparison node,
including its originally planned homogeneous and inhomogeneous comparisons.
No other module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a module with an unfinished proof. The current source
has zero holes and the current queue instead assigns its retirement. The retirement
row notes that the upstream twin lacks the old Nonempty theorem; its existing
additive-equivalence construction nevertheless implies that theorem directly.
No mathematics needs restating, weakening, or splitting.

Read the Stacks source Section 0DVG and the unit record. Mathlib searches through
msearch.py (LeanFinder, Loogle, grep) found definitions of continuous cohomology,
degree-zero and ordinary group-cohomology comparisons, with no exact profinite
resolution comparison. Direct rg on the adopted source found the exact stronger
replacement. The downstream tool lists six consumers, only one of which imports
or applies the retired theorem. Searches include quarantined sources. No archived
module or adopted-source declaration is deleted.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
