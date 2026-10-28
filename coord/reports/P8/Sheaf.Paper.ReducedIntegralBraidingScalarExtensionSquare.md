## What changed

Replaced the sole sorry in
`WeilConjectures.reducedIntegralBraidingScalarExtensionSquare` by a categorical
pasting proof using the existing `reduced_braiding` calculation. The statement,
universes, hypotheses and existing public imports are unchanged.

Added two proved component lemmas, each in its own new module:
`WeilConjectures.integralScalarTensorCoherentReduction` gives the coherent
scalar/tensor reduction equation without any braiding, and
`WeilConjectures.systemScalarTensorBraiding` proves compatibility of the
representative-normalized whole-system tensorator with signed symmetry.
The latter proof checks homogeneous tensor generators through the scalar
adjunction, localizes the equality on flat-term K-flat representatives, and
extends it by naturality to arbitrary derived systems. The former uses the
published normalized scalar realization, normalized scalar systems, counit
effectivity and tensor limit square. The main theorem combines these two actual
component equations with the defining reduction equations of integral braiding.

No existing definition or statement was changed. All additional imports are
private proof imports. All three Lean files compiled through the project compile service in import
order: coherent reduction in 31.8 s, system braiding in 27.6 s, and the item
in 12.0 s. All are below the 60 s per-file limit. The sole empty-line style
warning was removed before delivery.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.reducedIntegralBraidingScalarExtensionSquare` (1 of 1).
Also proved both new public lemmas
`WeilConjectures.integralScalarTensorCoherentReduction`
(node `lem-pur-integral-scalar-tensor-coherent-reduction`) and
`WeilConjectures.systemScalarTensorBraiding`
(node `lem-pur-system-scalar-tensor-braiding`), including their private helpers.
No sorry remains in the three delivered modules; no new hole is added.
This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

No existing public import was removed. The original module had no proof imports;
only imports used by the proof were added.

The main proof no longer directly needs the old planned dependencies
`lem-pc-kflat-resolution`, `lem-pur-coefficient-extension-reduction-model`,
`lem-pur-cochain-pullback-tensor-coherence`,
`lem-pur-normalized-scalar-comparison-realization`,
`lem-pur-normalized-tensor-constraint-transport`, or
`lem-pur-completed-primitive-counit-comparison`.
The fixed integral-braiding reduction equations already give the needed
constraint normalization. Scalar tensor normalization uses the current scalar
tower API, and the signed scalar square is proved directly on the entire
sequence site. The item node now records the actual component lemmas and
categorical reduction calculus instead.

In particular, no import of the absent
`Sheaf.Paper.NormalizedScalarComparisonRealization` is required. No withdrawal
is requested: K-flat resolution, coefficient extension and some geometric
modules remain used transitively by the component proofs or other library
consumers. Consequently there is no claim that any existing module has become
globally unreachable or may be deleted.

## Where the brief, the DAG or earlier work was wrong

The old proof plan records
`Sheaf.Paper.NormalizedScalarComparisonRealization`, which has no source file
in the current shared snapshot. The current scalar tower realization and limit
square APIs suffice, so no duplicate declaration or missing module was recreated.
The signed tensor flip is stated in Stacks `more-algebra.tex`,
`item-flip-tensor-product` (Koszul sign rules), rather than the old source
placement in `sites-cohomology.tex`. The proof uses whole-system maps and
naturality; it does not infer equality of derived morphisms from separate
finite evaluations.

The current blueprint unit `sk-def-purity-conv` has no realized statement or
proof-step attachments prescribing a different route. The component arguments
apply to zero objects, identity extensions and ramified quotient maps: scalar
coefficients have degree zero, and no quotient-flatness assumption is introduced.

## New nodes

`lem-pur-integral-scalar-tensor-coherent-reduction` records the natural
coherent reduction comparison and its tensor equation, with no symmetry in its
statement. Its sources are Stacks 07A4 and 0941 and the existing normalized
scalar and tensor realization interfaces. It is proved in
`Sheaf.Paper.IntegralScalarTensorCoherentReduction`.

`lem-pur-system-scalar-tensor-braiding` records the ordinary-derived
whole-system tensorator's signed-symmetry equation, without completed integral
objects or constructible comparisons. Its source is the Koszul signed flip in
Stacks `more-algebra.tex` together with scalar tensor balancing. It is proved
in `Sheaf.Paper.SystemScalarTensorBraiding`.

Both nodes record Lean Finder, Loogle and grep searches. Searches found generic
adjunction and sheaf tensor interfaces but no theorem identifying these specific
normalized comparisons. No change record is needed: no other existing module,
node, statement, definition or public import was adapted.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralScalarTensorCoherentReduction": "5daeffe5dabe4f2a61b162d09e011fd80c5d7034", "Sheaf.Paper.ReducedIntegralBraidingScalarExtensionSquare": "65550f03fbc73bc3a08fff0f0343b4e59857bb14", "Sheaf.Paper.SystemScalarTensorBraiding": "73dee3cc734aed4958885ff8757ba1e8473ad493"}, "results": {"Sheaf.Paper.IntegralBraidingScalarExtensionSquare": {"hash": "369859770a856cd86b884c202c075f6c43fa7c65", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T14:45:00+0800", "transitive": 0, "version": 1}
```

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
