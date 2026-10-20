## What changed

Completed the retirement listed in coord/retire-items.tsv for
Sheaf.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology.
The current item already has zero holes; this is an API migration and module retirement.
The existing adopted-source definition
Rep.invariantResolutionHomologyAddEquivInhomogeneous supplies an additive equivalence
with the same universes and hypotheses as the retired Nonempty underlying equivalence.

Migrated the only direct consumer,
Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology:
its private proof import now names the upstream module, and its proof obtains the
additive comparison, composes it with the homology comparison, then applies toEquiv.
Every public signature, public import and visibility in that consumer is unchanged.
No upstream module is modified.

Redirected the original DAG node's Lean attachment to the adopted-source definition.
Its mathematical statement, proof dependencies and parent edges remain valid: the
replacement proves the same comparison with its additive structure retained.
The named construction is not a new split or a choice from an unproved existence.

Change record: coord/changes/G1-retire-discrete-resolution-inhomogeneous.md.

## Proved and sorry left

The retired Rep.nonempty_equiv_invariantResolution_inhomogeneous already had zero holes.
Its old source compiled in 2.2 seconds; an axiom check compiled in 2.6 seconds and
reported exactly propext, Classical.choice and Quot.sound.

Holes closed: zero of zero. Holes added: zero. Split off: zero.
Rep.nonempty_equiv_invariantResolution_continuousCohomology remains proved using the
existing Rep.invariantResolutionHomologyAddEquivInhomogeneous construction.
There are no sorries in any delivered Lean file. The adapted direct consumer compiles
without warnings in 3.2 seconds through lcompile.py.

## No longer needed

Retired the entire redundant module
Sheaf.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology using deleted.txt.
Removed its direct proof import from DiscreteResolutionContinuousCohomology and replaced
it with WeilConjectures.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology.
The retired declaration and its local universal-delta-functor comparison are unnecessary.

No mathematical node or proof dependency is withdrawn. The original node and every
parent dependency remain attached to the actual upstream comparison. The upstream module
continues to use the integer invariants, cochain effacement, and universality modules;
this retirement does not claim those dependencies have been pruned. The unit sk-thm-br
and all its realized steps are preserved. There is no remaining direct library importer
or declaration use of the retired module outside the adapted consumer.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished proof, but the current source has no
sorry: W2's proof-only repair landed at 20261020T151237-L-2653854.
The applicable assignment is its row in coord/retire-items.tsv, whose API-difference note
says the upstream twin lacks the Nonempty theorem. The current upstream instead exposes
the stronger additive-equivalence construction, so the consumer can use it directly.
The initial unchanged-file dry run correctly refused a packet with no item change;
the final packet retires the module and migrates its actual consumer.

Mathlib searches via msearch.py: LeanFinder returned derived-complex comparison lemmas;
Loogle does not know the project's CohomologicalDeltaFunctor; hosted grep had no hit.
Direct rg on the adopted source located the exact replacement construction.
The downstream inventory lists seven downstream modules, including one direct importer;
no other file names the retired declaration. No new node or mathematical split is needed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
