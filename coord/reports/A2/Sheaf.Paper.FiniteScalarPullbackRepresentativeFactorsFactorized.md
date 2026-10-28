## What changed

Proved `WeilConjectures.finiteScalarPullback_representative_factors_factorized`
in `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactorsFactorized` without
changing its statement. The proof localizes the ordinary inverse-image square,
identifies its right mate using the already proved realization/direct-image unit
normalization, and transports the exact derived adjunction to the left-derived
adjunction. The final composition of localization factors is checked explicitly.

The four private helpers are proved categorical glue: equality of inverse mates
from the unit normalization, transport along the equality of coefficient direct
images, compatibility with an isomorphism of left adjoints, and the cochain
factorization of a localized square. Only this module and its own DAG node change.
No shared definition, public import, instance, attribute, or declaration signature
changes. The existing private helpers in
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` are accessed
with a private `import all`, and the direct-image unit-normalization module and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` are private
proof imports.

The source places read were Stacks Tags 07A6 (`lemma-adjoint`) and 0D6E
(`lemma-derived-pushforward-composition`). Cancellation of a right-derived unit is
used only at a K-injective complex. No faithfulness of localization is assumed.
The proof allows the zero ring, zero complexes, empty schemes, and arbitrary
unbounded complexes; none of these are excluded by a new hypothesis.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finiteScalarPullback_representative_factors_factorized`
(node `lem-sf-finite-scalar-pullback-representative-factors-factorized`).
Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.
No split-off statements or new modules.

Validation: the complete module compiled through `lcompile.py` in 51.7 seconds,
within the 60-second limit. The original theorem signature is byte-for-byte
unchanged; all Lean lines are at most 100 characters.

## No longer needed

Removed the private import
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit`:
the factorized equation can be proved directly, without rewriting its exactness
factors to a left-derived counit.

The planned dependency `lem-pur-exact-derived-mate` and its module
`Sheaf.CategoryTheory.DerivedExactMate` are unnecessary for this proof. The already
proved generic factorization and adjunction-transport helpers in
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` supply the
needed calculation directly. The DAG records those actual dependencies.
No module is withdrawn, and no claim is made that other consumers can omit these
modules. The blueprint unit statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The eight earlier decompositions did not need another
split: the library already contains the generic derived-mate factorization and
the bridge between exact and left-derived adjunctions. Combining these with the
existing all-complex direct-image normalization closes the obligation.
The DAG proof now specifies cancellation on K-injective representatives and the
naturality argument extending equality to every derived object.

The cross-unit nodes are used solely for already proved generic categorical and
K-injective-resolution APIs. They do not replace any step of the paper's unit.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarPullbackRepresentativeFactorsFactorized": "58542e177d52bd3e6195af65bc095817e133f1ad"}, "results": {"Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors": {"hash": "798964148f769d4cc5229bae38cf9f0a320cd023", "status": "OK"}}, "seconds": 93, "time": "2026-10-28T12:16:40+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
