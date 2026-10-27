## What changed

Proved `AlgebraicGeometry.marked_blowup_chart_smooth_baseChange` without changing its
signature. Four proved private helpers supply exceptional regularity, the principal
extended center ideal, injectivity of the flat chart comparison, and transport of
single-element ideal division. The existing comparison surjectivity and pure-tensor
formula finish the theorem. No other existing module is changed.

The colon calculation uses the given order bound: in the original chart the total
transform K lies in (e^c), so K = (e^c)(K:e^c). Map this factorization and cancel the
regular exceptional equation in the new chart. This avoids introducing a general
flat-colon theorem. Flat tensor preserves injectivity of multiplication by e; the
existing comparison-kernel theorem then supplies injectivity of the chart map.
All arguments include the zero ring, zero or unit centers, zero marked ideals,
nonfaithful smooth maps, and c = 1. The public hypothesis c >= 1 is preserved and used to obtain regularity of the
marking-th exceptional power from regularity of its generator.

Updated step 10 and the proof dependency union of
`lem-trf-marked-controlled-blowup-charts` to record the implemented affine proof.
The other three declarations and their planned proof steps are retained.

## Proved and sorry left

Closed one of the four original holes:
`AlgebraicGeometry.marked_blowup_chart_smooth_baseChange`.
Added zero holes; split off zero statements.

Validation: the complete module compiled without warnings through `lcompile.py`
in 11.3 seconds. `#print axioms` for the proved theorem reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The temporary audit command was
removed before delivery. All four original theorem signatures were checked to be
verbatim unchanged; the node's proof dependency list equals the union of step uses.

The three unchanged remaining holes, all attached to
`lem-trf-marked-controlled-blowup-charts`, are:

- `AlgebraicGeometry.smooth_marked_controlled_blowup`.
- `AlgebraicGeometry.smooth_marked_controlled_blowup_baseChange`.
- `AlgebraicGeometry.etale_coordinate_marked_blowup_charts`.

## No longer needed

The following private proof imports are removed because no completed proof in this
module uses them. The retained public imports supply its unchanged signatures;
`Mathlib.RingTheory.Flat.Basic` supplies the flat tensor injection used by the proof.

- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Mathlib.RingTheory.Regular.Flat`.
- `Sheaf.TraceFormula.SmoothGeometricallyNormal`.
- `Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents`.
- `Sheaf.AlgebraicGeometry.SmoothPairRegularEquations`.
- `Sheaf.RingTheory.RegularSequenceGradedPolynomial`.
- `WeilConjectures.Compactification.StrictTransformBlowup`.
- `WeilConjectures.Blowup.FiniteDegree.Algebra`.
- `Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation`.
- `WeilConjectures.Blowup.Affine.Principalization`.
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `WeilConjectures.Blowup.Proper`.
- `Sheaf.TraceFormula.EtaleRegularIntersectionDescent`.
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.Regular`.
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`.

No DAG node or module is withdrawn. In particular, the dependencies planned for the
three remaining holes are still needed by those plans and are retained in the node.
The closed source kernel and surjectivity nodes are added to step 10; their source
proofs and every declaration of the adopted source library remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. For the affine theorem, the existing docstring's
more general flat-kernel argument for colons can be replaced by the shorter ideal
factorization and cancellation argument above. The docstring now describes that
implemented proof. The brief explicitly permits one theorem of a multi-hole module
to be proved while the remaining theorems are unchanged.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
