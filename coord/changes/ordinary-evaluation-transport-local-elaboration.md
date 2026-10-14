# ordinaryEvaluation_component_over_transport

## Reason

Local elaboration attributes keep the proof on the abstract functor and equivalence APIs. The declaration-scoped unused-variable option addresses the linter warning for forall-bound hypotheses that are introduced and used by the proof. The theorem's signature and all existing definitions remain identical.

## Old

The original module has no local irreducibility attributes for the Hom-complex functor, open equivalence, unit comparison, or single-complex comparison, and no declaration-scoped unused-variable option.

## New

The module locally marks `homComplexFunctor`, `Scheme.Modules.overEquiv`, `Scheme.Modules.overEquivFunctorObjUnitIso`, `HomologicalComplex.singleMapHomologicalComplex`, and the new component construction irreducible. The theorem locally disables the unused-variable linter. These attributes are local and do not change the declarations or imported mathematical interface. The target's statement is unchanged.

The new summand/projection theorem has a declaration-scoped `maxHeartbeats 800000`
setting for its isomorphism and functoriality elaboration. The 60-second wall-clock
file limit is unchanged. The two transparency options are restored locally for
abstract calculations; the scheme component criterion is proved by unfolding its
formula, with the large Hom functor kept locally irreducible.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula | unclaimed | Existing theorem statement remains identical; proof imports and local elaboration attributes do not propagate. |
| Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentOverTransport | H4 | Proof uses abstract APIs and three smaller named steps (two proved and one admitted). |

## Status

landed 20261014T022546-L-4045870 2026-10-14 (merge of deliver/H4/Sheaf.AlgebraicGeometry.OrdinaryEvaluationComponentOverTransport)
