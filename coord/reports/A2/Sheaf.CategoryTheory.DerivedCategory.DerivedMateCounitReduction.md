## What changed

Replaced the proof hole in
`CategoryTheory.Adjunction.derivedPlus_mateEquiv_counit_reduction` with the node's
naturality calculation. Expand `mateEquiv_apply`, move the right-derived comparison
through the primed unit and the square, apply `derivedPlus_counit_app_fac`, and use
naturality of the exact localization comparison together with `hθ`. Finally move
the inverse comparison for `G` through the primed unit and cancel it by functoriality.
The statement, universes, definitions, public imports and unit route are unchanged.
All proof dependencies are already available through the existing public import;
no import or additional declaration is needed.

Validation: `lcompile.py` compiled the module cleanly in 4.3 seconds (exit 0).

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.Adjunction.derivedPlus_mateEquiv_counit_reduction`
(node `lem-trf-derived-mate-counit-reduction`). Added 0 holes and split off 0.
No `sorry` remains in the delivered module.

## No longer needed

None. No imports were removed and all three existing proof dependencies are used:
the adjunction mate, the bounded-below derived counit identity, and the exact
localization comparison. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows the five existing node steps. The naturality calculation
uses no inverse of the square or of either right-derived comparison and does not
require preservation of injectives by `H`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
