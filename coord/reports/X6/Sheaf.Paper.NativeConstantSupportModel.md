## What changed

In `Sheaf.Paper.NativeConstantSupportModel`, prove the ordinary-limit right-adjoint
structure and the uniquely unit-normalized derived-limit comparison. Identify the
actual coefficient restriction with the generic restricted tower construction via
the coefficient sequence's sectionwise uniqueness property. The ordinary proof
uses its existing extension/restriction adjunction and the diagonal/limit
adjunction. The derived proof uses acyclicity of restricted K-injective systems,
the canonical right-derived pullback comparison, and the derived universal
property for uniqueness. All original public signatures and definitions stay unchanged.

Add proof-only imports of `RestrictedTowerResolutionAcyclicity` (including its
proved private adjunction helper), `SystemEvaluationTopos`, and the source
library's `ShortExactPullback` API (which already imports `Comp`). The private local helper is proved;
it contains no hole. Update the item's proof record to describe these arguments.

Tool dependencies from other units: `lem-coef-restricted-tower-resolution-acyclicity`
provides precisely the restriction/limit acyclicity needed here;
`lem-pur-system-evaluation-topos` supplies additivity of the realization equivalence;
`def-sfb-preserves-kinjective-complexes` supplies the general equivalence criterion.
These are generic homological tools and do not bypass any unit step. No maintainer
`tool_uses` approval is added by this delivery.

## Proved and sorry left

Two of the six original holes are closed:

- `WeilConjectures.PurStrictScalar.ordinaryLimit_rightAdjoint`.
- `WeilConjectures.PurStrictScalar.reductionRightComparison_existsUnique`.

Four original holes remain, all attached to
`def-pur-native-constant-support-model`:

- `WeilConjectures.PurStrictScalar.systemProperOrdinary_existsUnique`.
- `WeilConjectures.PurStrictScalar.systemProper_existsUnique`.
- `WeilConjectures.PurStrictScalar.systemPullMap_isIso`.
- `WeilConjectures.PurStrictScalar.systemOpenMap_isIso`.

No holes are added or split off. The four remaining proof bodies are untouched.
The two completed proofs do not depend on those four holes.

## No longer needed

No original import, module or node is removed. The explicit proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` was
removed as redundant: `ShortExactPullback` already publicly imports it. The original node had no
numbered proof steps or proof dependencies to prune. Its statement dependencies
remain needed by the existing public interface and by the unfinished comparisons.

## Where the brief, the DAG or earlier work was wrong

The current node has an empty proof plan, so there are no numbered steps to
translate for these obligations. Existing proved restricted-tower constructions
supply a direct route. Scalar restriction need not preserve K-injectives; the
proof uses inverse-limit acyclicity instead. The two presentations of the quotient
ring system require the explicit limit-cone projection calculation and functor
identification; they cannot simply be treated as definitionally equal.

A related ordinary finite-scalar/direct-image proof landed in
`ConstantScalarTowerMates` during this session. Its ring-restriction comparison
provides a possible route for the remaining proper ordinary comparison, after
identifying the native varying-ring coefficient square and its horizontal maps.
It is not used to replace an unfinished obligation in this packet.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
