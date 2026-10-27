## What changed

Filled `AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_conjugate_computation`
without changing its signature. The proof pastes the separate tensor and scalar
computation squares on a termwise section image, using the supplied `he` and `ht`,
and cancels the resulting isomorphic prefix. Both final computation paths are
constructed as actual natural transformations, so naturality along the termwise
section equivalence's counit proves the equation for every section complex.
K-flatness and flat terms are transported along that counit explicitly.

Added `Sheaf.Paper.SectionTensorRightComputation` and
`Sheaf.Paper.SectionScalarComputationTransport`. The former constructs the actual
ordinary right-tensor comparison and its localization, and compares the tensor
representative map with tensoring a degree-zero coefficient. It uses the chosen total comparison’s summand equation directly in right
degree zero, together with the source-library formula for the inverse single-factor
comparison. A generic degreewise calculation proves this square without
constructing the full two-variable comparison natural transformation. The latter
compares scalar computation counits using the ordinary generator identities and exact restriction
localization factors. A proved ordinary tensor naturality lemma supplies the public data
definitions while keeping its proof import private. The original module imports
the computation results privately (the scalar module publicly imports the right-tensor module because its
statement names the localization).

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_conjugate_computation`
(`lem-sfb-section-tensor-conjugate-computation`), one of one original holes.

Added computation theorems:
`AlgebraicGeometry.ProEtale.QuotientChange.section_tensor_right_computation`
(`lem-sfb-section-tensor-right-computation`) and
`AlgebraicGeometry.ProEtale.QuotientChange.section_scalar_computation_transport`
(`lem-sfb-section-scalar-computation-transport`). Both are proved.

Holes closed: 1. Holes added: 0. Holes left in the delivery: none.
All three Lean modules have passed single-file compilation with `lcompile.py`.
The last scalar transport check took 47.8 seconds and the clean main-module check
47.2 seconds. Profiling options have been removed. The delivery tool performs the
final clean compilation and preflight.

## No longer needed

No original import or module is withdrawn. The proof does not invoke the full
`section_derived_tensor_normalization` theorem, previously named directly by the
node: the representative clause of `tensor_representatives` and the ordinary
comparison suffice. The geometric pullback, tensor-unit, associator and unitor
clauses of that normalization theorem are unnecessary for this scalar computation.
Its module remains a transitive private import of the existing
`ModuleRingedToposDerivedComparison` module, which supplies `ordinary_monoidal`;
no declaration or dependency in the adopted source tree has been removed.

The main theorem no longer invokes `internal_section_tensor_comparison` directly.
Its exact-equivalence and tensor constructions remain underneath the fixed
comparison data; the scalar square also reuses its proved local pure-tensor and
braiding component formulas, so its node remains a dependency of that square. The new proof dependencies
record the actual two computation squares and the site-tensor comparison used to transport flatness.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original first proof step combines two distinct
squares (tensor totalization with a single coefficient, and restricted scalar
computation). The source library already supplies the inverse-component formula for the
single-factor comparison in
`WeilConjectures.Algebra.Homology.BifunctorSingleComparison`. Together with the
existing summand characterization, this gives a direct calculation of the needed
right-coefficient square.
The final transport needs only isomorphism invariance of K-flatness and flatness,
not a new theorem asserting preservation of those properties by the internal
preimage functor. The argument covers the zero coefficient, zero complexes and
empty schemes, and introduces no coefficient flatness or boundedness hypothesis.

## New nodes

`lem-sfb-section-tensor-right-computation` records the tensor representative
square with a degree-zero right coefficient. It has no scalar comparison `s`,
no ordinary comparison `o`, no derived scalar isomorphism `e`, and no normalization
hypotheses; it is a separate tensor-localization compatibility result.

`lem-sfb-section-scalar-computation-transport` records the restricted scalar
counit square. It has no `e`, no conjugation hypothesis `he`, and no
`TensorNormalized` assumption `ht`. Its conclusion compares scalar counits and
ordinary tensor maps only. The main theorem supplies the derived tensor argument
and combines it with this square. Both nodes refine the existing unit route. All diagram-pasting and
generator-extensionality helpers used in their proofs are proved in the same modules. Generator extensionality is proved over a general site; the balanced-generator
calculation specializes the scalar-extension coequalizer and braiding formulas
to the pro-etale coefficient objects. The ordinary square composes these
component equalities explicitly, without unfolding the coefficient constructions
in rewrite matching.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
