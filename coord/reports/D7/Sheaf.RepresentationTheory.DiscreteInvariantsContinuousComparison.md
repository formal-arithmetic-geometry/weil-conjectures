## What changed

Retired Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison, an
explicit retirement item in coord/retire-items.tsv. The existing adopted-source
Rep.rightDerivedAddEquivContinuousCohomology has precisely the same universes and
hypotheses and constructs an additive equivalence. Its toEquiv supplies the exact
former Nonempty conclusion.

Adapted the two unclaimed direct callers, Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology
and Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding: replace their private
proof imports with the source module and use the constructed additive comparison's
toEquiv. Their statements, attributes, docstrings and public imports are unchanged.
No source-library file changes.

Retained lem-sc-discrete-invariants-continuous-comparison and reattached its Lean
record to Rep.rightDerivedAddEquivContinuousCohomology. Its mathematical statement,
proof dependencies and the unit route are unchanged. The node describes the
upstream construction followed by forgetting additivity.

Change record: coord/changes/D7-retire-discrete-invariants-continuous-comparison.md.

## Proved and sorry left

Initial item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in any delivered module. This is duplicate retirement, not a
new proof or a decomposition.

The exact old signature of Rep.nonempty_equiv_rightDerived_continuousCohomology
was separately compiled with proof
`exact ⟨(Rep.rightDerivedAddEquivContinuousCohomology G A E Γ η F N e he q).toEquiv⟩`.
Both this implication and the upstream construction have only propext,
Classical.choice and Quot.sound as axioms. The two adapted caller modules compile
cleanly (4.3 and 3.3 seconds). Every group, category, coefficient universe and
degree binder was retained in the exact-signature check.

## No longer needed

Withdrawn module:
Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison.
Removed declaration: Rep.nonempty_equiv_rightDerived_continuousCohomology.
Both direct callers drop their private import of that Sheaf module and use
WeilConjectures.RepresentationTheory.DiscreteInvariantsContinuousComparison instead.

The retired module's public imports and its private imports of
WeilConjectures.RepresentationTheory.DiscreteResolutionContinuousCohomology and
WeilConjectures.RepresentationTheory.ContinuousCohomologyCoefficientEquiv disappear
with that duplicate. Those source modules and their DAG nodes are still needed by
the upstream construction; no source declaration or mathematical dependency is
pruned. All existing DAG nodes, including the retired module's node, are retained.
Parent proofs continue citing the same node, now supplied by its upstream attachment.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item, but the current assigned item is
a zero-hole retirement repair. Its retirement row describes the different local
Nonempty declaration name; the source's additive construction is sufficient after
forgetting addition. This delivery performs that retirement rather than reporting
a no-op as a proof. No mathematical statement correction was required.

Searching lean/Sheaf, lean/WeilConjectures and quarantine found precisely the two
adapted uses; no quarantined parent imports the retired module. Both callers were
unclaimed when adapted. Parent DAG citations remain valid through the retained
node's new attachment, and the sk-thm-br unit route is preserved. No source-library
boundary exception is used. No new nodes or unproved object choices are introduced.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
