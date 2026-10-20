## What changed

Proved nine declarations in `Sheaf.Paper.LisseAdicSheaves`. Rational composition is
constructed by balanced tensor extension. Tensor lissity uses tensor right exactness
on stalks, and unit lissity uses the constant-sheaf stalk comparison. The coefficient
inclusion preserves spectral norms; the ramification index follows from the DVR ideal
classification. Rational scalar extension is constructed from the prescribed integral
functor by the additive tensor universal property, after proving its semilinearity
on the sheafified generators.

Added three proof-only imports: `WeilConjectures.ConstructibleSheaf.InternalHom`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`, and
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`. Added proved private helpers
and local instance caches. Generic quotient-map proofs and local opacity for the
stalk functor avoid repeated unfolding of large categorical constructions. Existing
public signatures, definition bodies and public imports are preserved.

Validation: the delivered module compiled in 38.9 seconds, and the unchanged direct
consumer `Sheaf.Paper.LisseIntegralSmallCoefficients` compiled against it in 2.9
seconds. The delivery compile, axiom probe and preflight passed. Preflight classified
the packet CODEX because the local caches add public declaration names.

## Proved and sorry left

Closed nine of the eleven original holes:

- `lisseRationalComposition_exists`
- `lisseIntegralTensor_isLisse`
- `lisseUnitModuleMap_id`
- `lisseUnitModuleMap_comp`
- `lisseIntegralUnit_isLisse`
- `lisseIntegerInclusion_exists`
- `lisseRamificationIndex_exists`
- `lisseScalarSourceIndex_le`
- `lisseRationalScalarExtension_exists`

Two original holes remain: `lisseIntegralScalarExtension_exists` and
`lisseCoefficientDiagram_exists`, both associated with
`def-pod-lisse-l-adic-sheaves`. Their declarations and existing proof docstrings are
unchanged. Zero holes were added, and no statements were split off.

## No longer needed

None. All original public imports remain part of the definitions' interface. The
three added private imports supply lemmas actually used by these proofs. No declared
DAG dependency or blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The definition node has no numbered proof steps or proof dependencies for the
remaining integral scalar-extension and coefficient-diagram existence theorems.
The nine completed proofs implement their existing docstring plans from the
available library and Mathlib APIs.

On resumption the launcher's budget metadata records start
`1792499300.8812675` (2026-10-20 12:28:20 UTC); the preserved earlier session record
had start `1792437810.9928522` (2026-10-19 19:23:30 UTC). This is the same F7 item
and sandbox following provider interruptions. The worker did not edit the budget
metadata or extend the original session deadline.

Preflight requested a change record for the four new public names of local instance
caches. Their instance attributes are local, and none has an existing named user.
The record is `coord/changes/F7-lisse-local-instance-caches.md`; no consumer is adapted.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
