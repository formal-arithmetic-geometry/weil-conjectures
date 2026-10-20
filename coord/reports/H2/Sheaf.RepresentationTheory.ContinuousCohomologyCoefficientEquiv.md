## What changed

Completed the queued retirement of
Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv, which already
contained zero holes. Its upstream counterpart provides
Rep.continuousCohomologyAddEquivOfCoefficients with the same hypotheses and a
stronger additive-equivalence result. The sole direct consumer,
Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison, now privately
imports the upstream module and takes `.toEquiv` from that construction. Its
public signature and public imports are unchanged. No upstream source is edited.

Reattached lem-sc-continuous-cohomology-coefficient-equiv to the existing upstream
construction and updated the consumer node's proof description. The original
node statement still follows by forgetting addition and taking Nonempty.intro.
The blueprint unit route is preserved. Change record:
coord/changes/retire-continuous-cohomology-coefficient-equiv.md.

Validation: the adapted consumer compiles with no errors or warnings through
lcompile.py. A separate compiler check of the upstream construction reports
exactly propext, Classical.choice and Quot.sound. Searches of both library roots and tools/downstream.py confirm the
complete direct-consumer set. The adopted upstream proof constructs the cochain
and quotient equivalences, including across distinct coefficient universes;
forgetting addition introduces no assumption or restriction on q (including q=0).

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in any
delivered Lean file. This is retirement of an already proved duplicate, not a
new proof counted by the sorry ledger. The retired declaration is
Rep.nonempty_equiv_continuousCohomology_coefficients; its obligation is met by
Rep.continuousCohomologyAddEquivOfCoefficients followed by `.toEquiv`.
Rep.nonempty_equiv_rightDerived_continuousCohomology retains its complete proof.

## No longer needed

Pruned module: Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv
(withdrawn using deleted.txt). Removed its sole import from
Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison, replacing it
with the private upstream import. The duplicate private helpers coindEquiv,
resolutionEquiv, resolutionEquiv_d, invariantsEquiv, cochainsEquiv,
cochainsEquiv_d, concreteData and shortComplexEquiv leave with the module;
upstream supplies the construction. No mathematical dependency node is pruned:
lem-sc-continuous-cohomology-coefficient-equiv is retained and reattached to its
upstream realization. No new node or dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes or a definition repair;
the current queue and coord/retire-items.tsv specifically classify this item as
retire, with zero holes and one direct consumer. The upstream API is named
continuousCohomologyAddEquivOfCoefficients and returns an additive equivalence,
so substituting only the import would leave the old theorem name unavailable.
The consumer's proof now explicitly forgets the additive structure. The old node
attachment named the duplicate local theorem and is updated accordingly.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
