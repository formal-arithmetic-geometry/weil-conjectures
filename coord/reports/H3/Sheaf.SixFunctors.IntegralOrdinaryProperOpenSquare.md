## What changed

Proved `WeilConjectures.IntegralSystemRealization.ordinaryProperOpenSquare` with its
original signature. Added the fully proved categorical theorem
`WeilConjectures.IntegralSystemRealization.ordinaryProperOpenConjugateSquare` in the
new module `Sheaf.SixFunctors.IntegralOrdinaryProperOpenCalculus`, together with private
proved calculus helpers and an explicitly constructed private inverse open coefficient
transformation. The item uses that module and the existing canonical coefficient-square,
adjunction, and open-effectivity APIs through proof imports. Updated the item's DAG
proof to match the Lean.

The proof derives the cartesian restriction square by adjunction conjugation, proves
the restriction-to-the-clopen-lift square from open composition and the inverse open
unit, and reuses the canonical clopen and proper-composition squares. It pastes the
five lambda factors, inverts the resulting square, transposes through the specified
open adjunction, and inserts the child's coefficient map by gamma naturality.
No completion or finite-level detection argument is used. Unit inversion is first
proved in abstract categories, so its concrete application does not unfold the derived
adjunctions. After that improvement, the proved calculus helpers occupy their own module
to keep the concrete proof computations small.

At the normalization boundaries a private metaprogram constructs explicit heterogeneous
congruence proofs and casts along their proposition equalities. In particular it uses
`Functor.comp_obj` before comparing objects of composite functors. This prevents the
kernel from comparing unrelated scheme categories before reducing the composition.
The generated terms are checked by the kernel; both transparency-respecting options
remain enabled. No shared definition or instance is changed. Two proved evaluation
identities for push and open extension handle the expression functors of the full
input family. The inferred private partial application is retained as a proposition
valued definition to preserve its exact dependent function type.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.ordinaryProperOpenSquare`
(node `lem-sf-integral-ordinary-proper-open-square`). Added zero holes; split off zero
statements. Every new helper is proved, and the private `openR` is constructed by
inverting the actual open reduction mate using the existing effectivity theorem.
No `sorry` remains in either delivered module. The new conjugation theorem is fully
proved and adds no proof obligation. Existing dependencies are used as stated.

Validation: the final item compiled cleanly through `lcompile.py` in 22.3 seconds;
the calculus module compiled cleanly in 23.2 seconds. Both are below the 60-second
per-file limit. The public theorem signature and both DAG Lean statement records
were checked verbatim against their corresponding declarations.

## No longer needed

No original Lean import was removed: the original public statement import remains.
The DAG dependencies `lem-sf-proper-open-lambda-reduction-square`
(`Sheaf.SixFunctors.ProperOpenLambdaReductionSquare`) and
`lem-sf-semilinear-proper-open-mate-pasting`
(`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`) are unnecessary for this proof.
The former concerns finite-field short words and completed/admissible inputs, whereas
this ordinary square is proved directly for arbitrary ordinary inputs. The latter's
intrinsic pasting laws are unnecessary because the supplied system and ringed gamma
adjunct fields already identify the actual lambda transposes. No declaration or
module is withdrawn; these results may have other consumers, and the bridge still
imports the intrinsic semilinear theory.

## Where the brief, the DAG or earlier work was wrong

The server queue currently assigns the restored module as a one-hole proof item.
The saved build error concerns an older unavailable
`IntegralOrdinaryExpressionReduction` import. The current source and published
coefficient APIs supply the dependencies needed by this proof.

The old DAG's completed short-word lambda theorem does not directly apply to the
ordinary expression statement: its finite-field, length and admissibility hypotheses
are absent here. The proof instead establishes the ordinary lambda square from the
already normalized primitive comparisons, without adding those hypotheses.

## New nodes

`lem-sf-integral-ordinary-proper-open-conjugate-square` records the fully proved
coefficient square for adjunction conjugation in
`Sheaf.SixFunctors.IntegralOrdinaryProperOpenCalculus`. Its proof applies the mate
bijection to the original square and uses Mathlib's two conjugation/composition
identities, then evaluates components. The module also houses the private proved
component calculus used by the item. No change record is needed: no other existing
module or node was changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryProperOpenCalculus": "e1ea88b0106a343107e9dcde48b557e537d68a9a", "Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare": "f0d6adc42bd47717ec04949fff491a06b0f29cc9"}, "results": {"Sheaf.SixFunctors.IntegralBasicGeneratorSquare": {"hash": "4688416ee2b87e73009b2dee904c25a31425339a", "status": "OK"}, "Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction": {"hash": "4cb63c4e27d0be274a5c4afb21fbc9031b6afbbb", "status": "OK"}}, "seconds": 78, "time": "2026-10-28T07:41:37+0800", "transitive": 1, "version": 1}
```

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
