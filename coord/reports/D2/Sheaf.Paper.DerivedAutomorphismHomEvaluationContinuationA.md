## What changed

Proved `WeilConjectures.podFiniteRestrictionOrdinary_existsUnique` by comparing
the intrinsic and sectionwise inverse-image adjunctions. The completed-ring
map agrees with the existing projection-normalized isomorphism. Its existing
scalar-restriction square, composed with left-adjoint uniqueness, gives the
required comparison. The left-adjoint uniqueness unit equation gives exactly
the displayed section normalization. For uniqueness, cancel the invertible
unit section maps, then use faithful precomposition by the base-change site
equivalence. This applies equally to the empty site, identity isomorphism,
and the first quotient level.

Proved `WeilConjectures.podSystemHomComparison_laws` without reducing equality
to separate finite evaluations. The specified sequence pullback is isomorphic
to the integral-comparison pullback; its identity and composition isomorphisms
exhibit inverse reindexing as a quasi-inverse. The closed adjunctions and tensor
comparison give a Hom bijection on image test objects, and essential
surjectivity plus Yoneda gives invertibility. The proved generic
`finiteChange_transpose` and `finiteChange_compatible` calculations are used
at their actual general signatures, which have no finite-coefficient or
constructibility hypotheses. The recorded tensor associativity and unit laws
build their required `CoreMonoidal` structure with precisely the prescribed
tensorator. Thus the proof uses the actual system evaluation and internal
composition, including unbounded inputs.

All signatures, definitions, public imports, instances and attributes are
preserved. No other Lean file changes. The shared parent node's proof steps
1 and 5 and proof dependencies record these implementations; the other
companions and their dependencies remain in its plan.

Validation: `lcompile.py` compiled the complete item in 38.2 seconds, including
both new proofs. Temporary profiling options were then removed and the three
reported long lines wrapped. Every theorem signature was compared with the
shared source and is unchanged. The four added DAG dependencies have no path
back to this node through statement or proof dependencies.

## Proved and sorry left

Closed two of the eight existing literal theorem holes; added zero holes and
split off zero statements:

- `WeilConjectures.podFiniteRestrictionOrdinary_existsUnique`
- `WeilConjectures.podSystemHomComparison_laws`

Six existing named holes remain, with their original source and proof docstrings:

- `WeilConjectures.podRationalClosed_existsUnique`
- `WeilConjectures.podRationalHomComparison_laws`
- `WeilConjectures.podCommonClosed_existsUnique`
- `WeilConjectures.podCommonHomComparison_laws`
- `WeilConjectures.podOrdinaryLimitReindexing_existsUnique`
- `WeilConjectures.podLimitReindexing_existsUnique`

These all retain blueprint `lem-pod-derived-automorphism-hom-evaluation`.
No definition contains a hole, and no declaration was weakened or renamed.

## No longer needed

The two proofs need no new resolution-model, K-injective, K-flat or derived
finite-evaluation lemmas. They use the existing adjunction and tensor APIs.
The following inherited private proof imports are removed from this module:

- `Mathlib.CategoryTheory.Adjunction.Additive`
- `Sheaf.Paper.PurInverseImageTensorHom`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses`
- `Sheaf.Paper.CompletedOperationTowerSubstitution`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`
- `Sheaf.Paper.SfDerivedCompleteLegacyComparison`

No whole DAG dependency is withdrawn: the shared node also owns untouched
companion modules whose proofs still use its original six-part plan. In
particular the remaining system reduction and limit assertions still use
`lem-pod-reindexing-system-hom-reduction-square`. Removing these private
imports does not claim their modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The queue snapshot lists nine holes, but the source copied for this item has
eight literal theorem holes: `podIntegralHomComparison_laws` was already a
complete assembly of its four component declarations. The actual count for
this delivery is therefore eight before and six after.

`Sheaf.Paper.ReindexingSystemHomReductionSquare` imports the parent
`DerivedAutomorphismHomEvaluation` and cannot be imported back here. The
system-Hom proof instead uses the acyclic general closed-adjunction calculation
and the already available coherent tensorator and inverse-reindexing APIs.
The four rational/common-stage obligations and the two limit normalizations
remain unchanged; their recorded descent and limit arguments need additional
glue beyond these two proofs.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA": "2e9552db49b2b434602492555058e2dfefccf892"}, "own_failed": ["Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA"], "results": {}, "time": "2026-10-28T08:10:04+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
