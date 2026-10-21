## What changed

Filled `WeilConjectures.localFrobeniusWeilMorphismNaturality` in
`Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` without changing its statement or any
existing definition. Proved private helpers for the specified rational composition
comparison, the single and iterated point transports, semilinear return comparison,
return transport, and iterated Weil-structure maps. The last clause follows by applying
the stalk/fibre functor to the iterated Weil-morphism equation and composing with return
transport naturality. All five clauses apply to arbitrary morphisms; no inverses of those
morphisms or extra hypotheses are used.

The composition naturality helper uses tensor induction and the published pure-tensor
prescription of `rationalDerivedPullback`, together with naturality of the published
integral composition isomorphism. Updated the item's DAG proof and proof dependencies to
record this route. No public interface changed; no consumer adaptations are needed. Preflight requests a
record for the scoped notation opening and local irreducibility commands; see
`coord/changes/local-frobenius-naturality-proof-elaboration.md`. The complete module
compiled cleanly through `lcompile.py` in 20.4 seconds. Local irreducibility attributes
keep elaboration from unfolding large pullback and fibre constructions; they do not
change any public definitions or the file timeout.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.localFrobeniusWeilMorphismNaturality`
(node `lem-fd-local-frobenius-weil-morphism-naturality`).

Holes closed: 1. Holes added: 0. Holes remaining in delivered modules: 0.
No statements were split off. Imported declarations with existing postponed proofs remain
dependencies, as allowed by the stage-3 brief.

## No longer needed

The proof does not use the private import
`Sheaf.Paper.IntegralPullbackComparisonRealization`, corresponding to
`lem-trf-integral-pullback-comparison-realization`. Its broad realization, associativity,
scalar-extension, and finite-iteration coherence theorem is unnecessary here: naturality
of each comparison follows directly from its actual localized integral formula, and
induction follows the given recursion one successor at a time. This removes that proof
edge for this item only; it does not assert that other consumers can prune that module.
The node's statement dependencies and the unit's route are preserved.

No other imports, nodes, or modules are pruned, and no modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG plan described rational composition naturality as supplied by the broad
realization-coherence theorem, whose stated naturality field concerns a different
realized integral family. The concrete `localPullbackComposition` can instead be handled
directly using its published integral natural isomorphism and rational tensor-Hom map
formula. This avoids identifying distinct chosen comparison families. No mathematical
statement or target was corrected.

Searches through LeanFinder, Loogle, the project's search wrapper, and local `rg` found
only generic naturality and endofunctor-algebra results, not a theorem of the five
specified local constructions. The generic naturality and equality-transport tools are
used in the proof. The existing unit record has no realized proof steps to bypass.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
