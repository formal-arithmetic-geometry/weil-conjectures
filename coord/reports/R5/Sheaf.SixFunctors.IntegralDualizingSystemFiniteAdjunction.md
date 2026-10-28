## What changed

The original statement and all its binders remain unchanged. Its proof now obtains
a normalized system trace, constructs a specific exceptional comparison, proves
componentwise invertibility by exact finite evaluation, and applies `asIso`.

Added `IntegralDualizingSystemAdjunctionMap`: the proper projection/evaluation word
before base sections, its two adjunction transposes, a complete proof of
contravariant naturality, exact scalar-tower evaluation, and joint conservativity
proved directly using homology. These constructions contain no chosen witness
from a holed existence theorem.

Added `IntegralDualizingSystemTraceData`: the finite exceptional counit transported
through the fixed dualizing origin and the actual compact-support site comparison;
a trace structure whose finite normalization is an explicit equation; and the
resulting natural transformation. The structure is parameterized data, not a
choice-based definition. The target proof eliminates its existence proposition
locally. No existing module besides the assigned item was changed.

The geometric work is separated into two genuine steps: construction of a
normalized trace on Q (no test input and no Hom isomorphism), and invertibility of
one finite evaluation of its explicitly defined transpose (no naturality or tower
assembly). Both retain the original finite exceptional adjunction route.

## Proved and sorry left

This is a decomposition, not a net proof gain. The original hole in
`WeilConjectures.integralDualizing_system_finite_adjunction` is replaced by a
complete combining proof. One original hole is closed and two holes are added
(net minus one); no `sorry` remains in the assigned module or in a definition.

The finite statements were checked at n = 0 (the positive coefficient exponent
is n + 1), at the zero input, and on an empty scheme. In the latter cases
the comparison is between zero Hom objects.

The two new holes are:

- `WeilConjectures.integralDualizingSystemTraceData_exists`, node
  `lem-coef-system-dualizing-trace-existence`.
- `WeilConjectures.integralDualizingSystemAdjunctionMap_evaluation_isIso`, node
  `lem-coef-system-exceptional-transpose-finite-isomorphism`.

The projection mate naturality, inverse open-tensor naturality, base-pairing
dinaturality, closed transposition naturality, whole-system comparison naturality,
finite etale bounded-below property, and exact tower detection are proved.

Validation: the complete sandbox is compiled in import order by `lcompile.py`;
the delivery command supplies the final compile, preflight and axiom checks.

## No longer needed

No existing import was removed. No existing module is withdrawn.

The direct dependency on `lem-weil-pbc-sequential-tower-evaluation-full`
(`Sheaf.CategoryTheory.SequentialTowerEvaluationFull`) is unnecessary: the map is
constructed explicitly, and joint detection is proved directly from exact
evaluation and homology. No family of finite isomorphisms is independently lifted.
This is only a pruning of this proof route; the module may have other consumers.

The other old geometric dependencies remain under the two new step nodes:
`lem-coef-finite-exceptional`, `lem-coef-finite-dualizing`,
`lem-weil-finite-duality-site-comparison`, `prop-asd-internal-adjunction`, and
`lem-coef-integral-residue-tor`. They are not claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The named dependencies describe the finite geometric comparisons, but they do
not directly provide a natural transformation between the displayed system-Hom
functors. In particular tower-evaluation fullness cannot supply naturality in K.
The delivered explicit projection/transpose calculation supplies that missing
glue. The two remaining geometric statements retain the supplied finite origins
and counits, so this does not use the older disputed arbitrary-trace currying
route. No target or existing statement was weakened or changed.

## New nodes

`def-coef-system-exceptional-transpose` records the explicit projection/transpose
construction, its proved naturality, and exact scalar-tower detection.

`def-coef-system-dualizing-trace-data` records finite-counit normalization data and
the natural transformation constructed from a trace. Its finite counit is an
actual composite of existing maps.

`lem-coef-system-dualizing-trace-existence` records the still-open construction of
a counit-normalized trace on the single Q. It does not assert any Hom isomorphism.

`lem-coef-system-exceptional-transpose-finite-isomorphism` records the still-open
finite exceptional adjunction calculation for one input and one level of the
specified map. It does not assert naturality or a whole-system isomorphism.

No change record is needed: no other existing module, definition, or statement
was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingSystemAdjunctionMap": "50bb2299c41a57f870c4740d07dfba3bd7de7aba", "Sheaf.SixFunctors.IntegralDualizingSystemFiniteAdjunction": "089f32d123ab1979fdaf50fafdb17da127f87426", "Sheaf.SixFunctors.IntegralDualizingSystemFiniteEvaluation": "1f7df5bcf845495fbcdfac0899ca25206d95e7bd", "Sheaf.SixFunctors.IntegralDualizingSystemTraceData": "ef6bdedb20d4135c3f35be5ac178bd17e2fba809", "Sheaf.SixFunctors.IntegralDualizingSystemTraceExistence": "e1668031b4bc21ff36b6d2760ddb91c7cda24509"}, "results": {}, "time": "2026-10-28T12:26:27+0800", "transitive": 0, "version": 1}
```

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
