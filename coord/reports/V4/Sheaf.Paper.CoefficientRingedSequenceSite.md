## What changed

Completed the proofs in `Sheaf.Paper.CoefficientRingedSequenceSite`, retaining the
interrupted session's work and closing the remaining strict restriction construction.
All existing public statements, definition bodies and visibility are unchanged.

The topology and sheaf proofs use vertical slices. Evaluation uses continuous
module pushforward, its sectionwise descriptions and componentwise exactness.
The quotient transition is the module pushforward transformation along the actual
horizontal arrow; uncurrying identifies its scalar map with the recorded quotient.

For strict completed-scalar restriction, compose the actual completed-ring limit
projections with the evaluation ring identifications. The limit cone equations
make the horizontal maps completed-linear. These module pushforwards form an
actual strict tower; its identity, composition and naturality laws follow from
those of the original module presheaf. The prescribed component objects and
section maps determine the functor uniquely. A generic composition lemma avoids
unfolding concrete coefficient rings to identify the component module structures.

Restriction exactness is checked by evaluation at each level. A separating family
for diagram categories supplies the Grothendieck structure and hence K-injective
resolutions of constant towers. Inverse-limit additivity follows by composing
with its projections. The derived projections use the right-derived universal
property, cancellation of its invertible unit on K-injectives, and essential
surjectivity of K-injective representatives for uniqueness.

The restriction/evaluation theorem is moved before restriction exactness, which
uses it. Private helpers are fully proved. Updated the existing DAG node's proof,
proof dependencies and proof origin to record this route. No new nodes or modules.

## Proved and sorry left

Closed all 15 original holes, with zero holes added or split off:

- `WeilConjectures.coefficientSequenceTopologyAxioms`
- `WeilConjectures.coefficientSequenceCommRingPresheaf_isSheaf`
- `WeilConjectures.coefficientSequenceEvaluationContinuous`
- `WeilConjectures.coefficientSequenceEvaluationRing_eq`
- `WeilConjectures.coefficientSequenceEvaluation_exact`
- `WeilConjectures.coefficientSequenceEvaluation_additive`
- `WeilConjectures.coefficientSequenceEvaluationAb_eq`
- `WeilConjectures.coefficientSequenceRestrictedEvaluationAb_eq`
- `WeilConjectures.coefficientSequenceTransition_exists`
- `WeilConjectures.coefficientSequenceRestriction_exists`
- `WeilConjectures.coefficientSequenceRestriction_exact`
- `WeilConjectures.coefficientConstantTowers_haveKInjectives`
- `WeilConjectures.coefficientConstantTowerLimit_additive`
- `WeilConjectures.coefficientConstantTowerProjection_exists`
- `WeilConjectures.coefficientSequenceRestriction_evaluation`

No `sorry` remains in the delivered module. The proofs use existing imported
statements; no imported theorem's proof or signature is changed.

The complete module compiled without errors or warnings through `lcompile.py`
in 38.3 seconds. The constructions admit equal tower indices, index zero, empty
schemes, zero modules and unbounded complexes without additional hypotheses.

## No longer needed

Removed unused proof-only imports:

- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Algebra.Homology.TowerEvaluationKInjective`

Their lemmas are unnecessary here: exactness is proved by evaluation and
forgetful functors; K-injective resolutions follow from the Grothendieck
structure of the diagram category; derived projections use the right-derived
universal property directly. The separating-family argument replaces an unused
comparison with modules on a constant ringed sequence site. No modules are
withdrawn, no previously declared proof dependencies are dropped (the repository
node had none), and no unit step is bypassed. Public imports retain the existing
statement interfaces.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox had 14 of 15 original holes closed but had not been delivered.
The remaining construction now has a proof: actual limit-projection compatibility
supplies the completed-linear transition maps, and sectionwise extensionality
supplies strict uniqueness. The retained report's account of open transition and
derived-projection constructions was stale and has been replaced.

The repository node had an empty proof plan. Its sandbox copy now records the
implemented arguments and their two non-elementary library dependencies. No
mathematical statement, definition or consumer needed repair. The first dry run
found a misplaced heartbeat-limit explanation; it was moved to the location the
linter requires. Subsequent elaboration issues were resolved with generic
composition and explicit extensionality arguments, without changing definitions
or the single-file time limit. Scratchpad experiments are excluded from delivery.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
