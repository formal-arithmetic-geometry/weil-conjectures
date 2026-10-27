## What changed

Implemented `AlgebraicGeometry.ProEtale.NativeFrobenius.nativeFrobeniusComparison`.
The proof constructs inverse-pushforward translation through the actual site
isomorphism and checks the required internal-Hom equation on evaluations of
sections. Its statement and the specified ordinary model are preserved.

Three new proved companion modules keep the concrete section construction,
equivalence/counit calculation, and tensor-evaluation calculations separate:
`Sheaf.Paper.NativeFrobeniusSectionTransport`,
`Sheaf.Paper.NativeFrobeniusHomEvaluation`, and
`Sheaf.Paper.NativeFrobeniusEvaluationCalculus`. The item imports the first and
third privately; section transport uses the Hom-evaluation module's section counit.
The DAG records the actual proof dependencies.

Validation: all four modules passed server compilation. The final delivery
runs the compiler and axiom probes again after removing diagnostic output.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.NativeFrobenius.nativeFrobeniusComparison`.

Added zero holes; split off zero unproved statements. Every declaration in the
three companion modules has a complete proof or a concrete data construction.
The public proved helpers are `nativeFrobeniusSectionTransport`,
`comparison_evaluation`, `evaluation_ext`, `evaluation_map_source`,
`evaluation_map_target`, `evaluation_restriction`, `pushforward_evaluation`, and
`translated_evaluation`, all in namespace
`AlgebraicGeometry.ProEtale.NativeFrobenius`.
There are no remaining `sorry` declarations in this delivery.

## No longer needed

No module is withdrawn and no existing public import is removed. The proof uses
the fields of the given presentation from
`def-sf-twisted-action-presentation-data`; it does not invoke the existence result
`lem-sf-twisted-action-ringed-site`. That existence module remains in the import
closure through the existing model's `WeilFrobeniusActionResolutions` import, so
this delivery claims no module pruning. The original model, section-module
equivalence and normalized Hom comparison remain needed.

## Where the brief, the DAG or earlier work was wrong

None. The original route works by the concrete section construction followed by
native and ordinary evaluation. An explicit identification of the sheaf tensor
comparison with the forgetful lax tensor map avoids expensive definitional
reduction; no shared definition or interface needs repair.

## New nodes

`lem-sf-native-frobenius-section-transport` realizes the concrete site/scalar
identification and its normalized section formula in
`Sheaf.Paper.NativeFrobeniusSectionTransport`. It is proved.

`lem-sf-native-frobenius-hom-evaluation` realizes counit normalization of the fixed
small-site/native Hom comparison in `Sheaf.Paper.NativeFrobeniusHomEvaluation`.
It is proved, using generic equivalence and counit identities.

`lem-sf-native-frobenius-evaluation-calculus` realizes the native evaluation
criterion, functoriality, restriction and pushforward formulas, and the ordinary
presentation's identity-slice evaluation formula in
`Sheaf.Paper.NativeFrobeniusEvaluationCalculus`. All are proved.

No change record is required: no existing module besides the assigned item,
and no existing node besides its node, is changed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
