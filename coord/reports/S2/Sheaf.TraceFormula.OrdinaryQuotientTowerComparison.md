## What changed

Restored the assigned quarantined module and replaced the whole proof of
`WeilConjectures.ordinaryQuotientTowerComparison`. Its statement and two public
imports are unchanged. Added proof imports of IntegralOperationRoosEffectivity,
CoefficientSequenceRoosModel, IntegralOperationsWellDefined and
CompletionUnitOrdinaryAdjunction. Proved private
helpers adapt the existing finite comparison and quotient-mate argument to
independent site and coefficient universes. The proof assembles the strict tower
isomorphism and proves the presentation section formula by actual inverse cancellation.
The finite comparisons use recorded object equalities and the explicit scalar-restriction
composition isomorphism, avoiding large functor-equality transports. The unit-tensor
formula reuses the existing ordinary-adjunction lemma.
Only the assigned module and its node change. All four proof-imported modules
are already in the original public imports’ transitive closure; these imports
make their existing private helpers available without expanding that closure.

## Proved and sorry left

Closed: `WeilConjectures.ordinaryQuotientTowerComparison`
(node `lem-trf-ordinary-quotient-tower-comparison`), the sole original hole.
Added holes: none. Remaining holes in this module: none. Every private helper is proved.

Verification: lcompile.py compiled the complete module in 34.1 s without profiling
options. `#print axioms` reports exactly `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorryAx`. The theorem statement matches the archived
assignment verbatim. The new imports are proof-only, and no shared interface changes.

## No longer needed

No original imports or declared dependencies were removed. No module or node is
withdrawn. The existing derived calculus assembly theorem, good-complex hypotheses,
Roos normalization, completeness and boundedness are not invoked by this ordinary
comparison; only the ordinary coefficient interfaces and existing proved helper
lemmas are used. No additional split-off obligations are introduced.

## Where the brief, the DAG or earlier work was wrong

The module was absent from lean/ because of the listed build quarantine, not
withdrawn. It is restored from its recorded archive. The existing comparison
argument in IntegralOperationRoosEffectivity specializes to equal site and
coefficient universes; its generic categorical helpers can be reused, but its
specialized finite comparison cannot directly prove this independent-universe
statement. The local helpers supply that generalization without modifying any
shared definition or consumer. The unit route is unchanged.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
