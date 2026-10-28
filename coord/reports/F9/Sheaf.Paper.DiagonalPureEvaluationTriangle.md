## What changed

Replaced `AlgebraicGeometry.ProEtale.diagonal_pure_evaluation_triangle`'s proof hole
with the common-resolution multiplication-sequence argument. Its statement, the
`PureEvaluationTriangle` predicate, and `diagonalPureEvaluationIso` are unchanged.
The supplied evaluation unit and the supplied purity isomorphism determine the
middle arrow exactly.

Four new proved helper modules isolate the regular representative, the actual
quotient-unit short exact sequence, the exact-derived transformation comparison,
and the abstract extraction of ordinary compatible boundaries. The item has only
private proof imports of these helpers. No existing module besides the item is
changed, and no adopted source-library declaration is changed. The generic
comparison algebra and gluing proof are private lemmas of the item; keeping this
work generic avoids repeated kernel reduction of the concrete sheaf categories.

Validation: all five Lean modules compile individually without warnings. The final
unprofiled item compile took 52.6 seconds; helper compiles took at most 26.6 seconds.
All files satisfy the 100-character line limit and contain no proof holes or
profiling options.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.diagonal_pure_evaluation_triangle`.

The new results are proved:
`diagonal_reduction_resolution`, `diagonal_evaluation_complex_shortExact`,
`exactDerivedTransformation_app`, `exactDerivedTransformation_commShift`,
`exactDerivedTransformation_single`, `exactDerivedTransformation_shiftedSingle`,
and `pure_multiplication_triangle_assembly` (all in namespace
`AlgebraicGeometry.ProEtale`). The auxiliary complex-map component formula is
also proved. The four helper modules add zero holes. No `sorry` remains in any
Lean file in this delivery; zero statements were split off with `sorry`.

## No longer needed

No original Lean import is removed: both original public imports are retained.
The planned dependency `lem-pur-constant-two-term-resolution`, module
`Sheaf.Paper.ConstantTwoTermResolution`, is unnecessary for this argument and is
not imported. A torsion-free common representative and the existing ordinary
quotient comparison directly give the required short exact sequences.

The planned direct dependency `lem-pc-kflat-resolution`, module
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, is replaced by
the existing generic flat-term resolution and derived-reduction resolving-class
machinery. The independent-coefficient resolution module remains in the transitive
import closure through existing libraries; this delivery does not withdraw it.
No existing declaration or module is deleted, and no unit statement or unit proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement repair is needed. The old proof plan required the simultaneous
counit computation for an arbitrary supplied reduction and the coherence of the
canonical evaluation, single, and shift comparisons; these are now supplied as
proved steps rather than new proof obligations. In particular, the ordinary
quotient comparison already proved in `DiagonalReductionCompletion` avoids
reconstructing the two-term coefficient resolution. Only its existing private
`ordinary_level_comparison` is used, not the completion conclusion.

The proof uses one representative at all levels. It does not infer naturality
from separate distinguished triangles or assume evaluation is faithful on
arbitrary derived morphisms. The multiplier is obtained from the actual
short-exact-sequence map with components `(ell, identity, quotient)`.

## New nodes

`lem-sfb-diagonal-reduction-resolution` records the common regular representative
and invertibility of the supplied counit, proved using the existing resolving
class and uniqueness of left derived functors.

`lem-sfb-diagonal-evaluation-complex-sequence` records short exactness of the
actual underlying quotient-unit complex map, transported from the integral
cokernel comparison in each degree.

`lem-sfb-exact-derived-transformation` records localization of a termwise
transformation and its compatibility with the standard single and shift
comparisons. Its degree-zero square is proved termwise, and its shift square
uses shift compatibility and essential surjectivity of localization.

`lem-sfb-pure-multiplication-triangle-assembly` records extraction of ordinary
boundaries by full faithfulness of shifted singles and the boundary identity
from naturality of short-exact triangles. This is a generic lemma, proved for
any natural-number multiplier and any abelian category with a derived category.

All new statements were checked at zero objects; the generic assembly allows
ell = 0 or 1 because its short exact sequences are hypotheses. The concrete
resolution and quotient results retain the original prime hypothesis and apply
at n = 0 without a special case. No change record is needed because no existing
statement, definition, instance, attribute, or public import changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalEvaluationComplexSequence": "37f1a2eb13a6a52be2bff0a1b03d1d9cb37a172c", "Sheaf.Paper.DiagonalPureEvaluationTriangle": "e71cc5ba019383434a3da22c64ae0e09654810a3", "Sheaf.Paper.DiagonalReductionResolution": "75ca3f1992e4a6b216214ca2add45ec6320d83c0", "Sheaf.Paper.ExactDerivedTransformation": "01b1dc10db08c5cb137e8d9a40f0f8ee199ae1c9", "Sheaf.Paper.PureMultiplicationTriangleAssembly": "fdf3b70d89a38756d846ab9e9023d0da43af0eba"}, "results": {"Sheaf.Paper.KummerPureKernelNormalizationData": {"hash": "91d8ec7615a994f6f5e4d8ccde9640fbd28b774e", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T10:48:17+0800", "transitive": 0, "version": 1}
```

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
