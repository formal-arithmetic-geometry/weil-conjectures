## What changed

Proved `WeilConjectures.ProjectionTensorCoefficient.ordinary_existsUnique` by applying
`tensorComparisonDescent` to the actual signed-total coefficient isomorphism.
Restriction of the derived localization to flat-term K-flat representatives is a
localization by the existing good-complex localization theorem. The normalization
and its converse follow by composing with, and cancelling, the target representative
inverse. Naturality of the signed-total comparison is supplied by the existing
proved `tensorPullbackTotal_naturality` in `RingedTopoiCanonicalTensorPullback`,
specialized in a private helper. Tensor-map factorization is also performed at the
generic categorical level. The descent and normalization cancellation are combined
in a proved generic helper before specialization.

The existing `good` proof is preserved. The argument of `completion_isIso` is
preserved. A proved generic logical helper drops the unused chain and augmentation
data before the rest of that argument; the final transport-and-composition step is
factored into a proved private categorical lemma to reduce conversion cost. The
selected ordinary comparison is declared after this independent proof. The ordinary
and rational normalization predicates are named without changing any clause,
reducing repeated type checking in the selected comparison definitions. Both old
statements are definitionally identical after unfolding their predicates. Existing
construction bodies and public imports are preserved. The change record is
`coord/changes/J8-projection-tensor-normalization-predicate.md`; no downstream
module needs adaptation.

Validation: the submitted module compiled through `lcompile.py` in 50.9 s with
no errors or debug options. Both new imports pass `import_direction.py may`.
The ordinary and rational normalization clauses are token-identical to their
original inline predicates after ignoring whitespace. The 107 downstream modules
require no adaptation; the selected comparison definitions keep their types and bodies.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.ProjectionTensorCoefficient.ordinary_existsUnique`.
No holes added. The private signed-total naturality helper is proved.

Two original holes remain (the rational predicate is only named, with identical content),
both attached to
`def-sf-projection-tensor-coefficient-comparison`:

- `WeilConjectures.CompactSupportCoefficientTensor.integral_existsUnique`
- `WeilConjectures.CompactSupportCoefficientTensor.rational_existsUnique`

## No longer needed

No existing dependency node or library module is withdrawn. The previous attempt's
unlanded split drafts are retained in the sandbox scratchpad, outside the delivery:
coefficient-factor invertibility is already a natural-isomorphism instance;
signed-total naturality follows from the existing proved generic helper; and the
proposed normalization-square hole is replaced by direct composition and cancellation.
No new nodes or split-off holes are needed for this proof.
The draft import of `ScalarHomTensorComparison` is unnecessary: the same proved
generic naturality and map-factorization lemmas are available in the already-needed
`RingedTopoiCanonicalTensorPullback`. No new scalar-Hom dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The previous attempt treated dependent full-subcategory proof transport as an
obstruction to finishing ordinary normalization. The descent theorem can be applied
with exactly `good` as its preservation certificate. Composing its equation with
the same representative inverse, and cancelling that inverse for uniqueness,
avoids any separate transport assertion. The two draft nodes had copied the entire
parent statement and review metadata; they are not submitted as mathematical nodes.
The unit route and all target statements are unchanged.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
