## What changed

Proved `WeilConjectures.LocallyFiniteAdicRealization.nativeIntegralCoefficient_heart`
in `Sheaf.Paper.NativeIntegralCoefficientHeart`, preserving its complete signature
and all three public imports. Added only proof imports and proved private helpers
for lifting section-ring maps to internal ring maps and transporting stratified
local models across an isomorphism. No existing module besides the assigned item
was changed.

The inverse of the fixed integral section equivalence gives an internal integral
module with the supplied finite constant local models. The existing
`integralSectionLocalModels` and the proved easy direction
`constructible_of_finiteConstantStratified` turn these into internal
constructibility. A restriction square built from `sectionModuleComapIso` gives
an extension square by `isIso_inverseMate_of_equivalences`. This identifies the
ordinary scalar extension in the hypothesis with internal scalar extension.
The proved ordinary `constructible_extend` preserves constructibility, and
`encoding_constructible_iff` reflects it back to the native sheaf.

Updated the assigned node's proof, proof dependencies and proof origin to this
argument. No statement, definition, instance or public import was changed. The
unit's route is preserved; this is its existing ordinary coefficient-passage
step.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.LocallyFiniteAdicRealization.nativeIntegralCoefficient_heart`
(node `lem-sf-native-integral-coefficient-heart`).

Holes closed: 1. Holes added: 0. Split-off statements: 0. Remaining `sorry`s in
the delivered Lean module: 0. Both private helper theorems are proved, and the
private definition is an explicit forgetful-functor construction.

Validation: the complete file compiled in 9.9 seconds with both
`backward.isDefEq.respectTransparency` options enabled. The original theorem
signature was compared verbatim, and the updated DAG dependency list is exactly
the union of its proof-step uses.

The proof uses only the already proved helpers in
`IntegralLfpConstantModelComparison` and `BoundedConstructibleExtendScalars`,
not their stronger integral-converse or derived conclusions. It makes no
flatness assertion and chooses no finite basis or arbitrary unproved witness.
Empty schemes, empty strata, zero modules and torsion scalar models are handled
by the existing constant-model and finite-presentation predicates.

## No longer needed

The proof does not need the planned nodes
`lem-weil-pbc-continuous-integral-model-encoding-universes`
(`Sheaf.Paper.ContinuousIntegralModelEncodingUniverses`) or
`lem-sfb-internal-section-scalar-adjunction`
(`Sheaf.CategoryTheory.InternalSectionScalarAdjunction`). They were removed
from this node's proof dependencies and were not imported: the fixed section
equivalence, its restriction comparison and inverse mates replace them.
These are removals from this proof's route, not withdrawals of those modules;
other consumers may still need them.

The separate proof import of
`Sheaf.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars` was removed
because the used ordinary scalar-extension helper already imports it. Its
finite-presentation result remains an indirect dependency and is retained in
the DAG. No original public import was removed. No module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan was longer than necessary: the existing fixed integral
section equivalence and its proved local-model comparison already supply the
needed bridge. The restriction square determines the extension square by
adjunction mates, so the separate continuous integral encoding and scalar
adjunction obligations need not be proved for this item. The original statement
is unchanged and no false-statement or process defect was found.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeIntegralCoefficientHeart": "80be186490d4e668e6baf6f09f69321445a987c4"}, "results": {"Sheaf.Paper.NativeIntegralTensorConstructible": {"hash": "e5f23908ad5c3e5db73735f350561d232959aeff", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T14:13:44+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
