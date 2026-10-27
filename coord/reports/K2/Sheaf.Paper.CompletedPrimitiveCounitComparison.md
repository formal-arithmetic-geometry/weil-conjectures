## What changed

The comparison-existence hole is reduced to two genuine realization subarguments:
primitiveCounitTensorRealization and primitiveCounitPullbackRealization. Their
statements retain the full strict representative model normalizations. Each lives
in a new module with one theorem and has a source, detailed proof and DAG node.

completedPrimitiveCounit_comparisons_exists now assembles every field in Lean.
Counit effectivity is transported from the existing normalized reconstruction
calculus by left-adjoint uniqueness. Exact derived composition gives geometric
evaluation. Functoriality proves invertibility; composites of actual isomorphisms
give both prescribed inverse words. Naturality is naturality of whiskered counits
and realization maps, using the product of counits for tensor. Projection equations
are the existing natural transformations' naturality equations.

completedPrimitiveCounit_roos_exists is proved from the canonical Roos construction.
The new coefficientConstantTowerRoosNormalization theorem retains its defining unit
equation and derives the full resolution normalization by naturality. It is proved
and adds no hole.

The pre-existing model declarations through PullModel are relocated verbatim to
PrimitiveCounitComparisonModels. The original module publicly imports them, so
all names, signatures, values and public availability are preserved. The existing
definition owner def-sf-primitive-tensor-realization-data points to their new file;
its Lean signature records the existing abbrev presentation. No consumer source
adaptation is included. The change record is
coord/changes/K2-primitive-counit-model-source-separation.md.

## Proved and sorry left

Current item baseline: two holes. Closed:

- WeilConjectures.completedPrimitiveCounit_roos_exists, by the explicit canonical
  Roos construction retaining its derived-unit equation, then naturality on every
  K-injective resolution.
- WeilConjectures.completedPrimitiveCounit_comparisons_exists, by decomposition
  through the two realization statements and the complete assembly proof.

Two holes added and left, each strictly a realization part of the original argument:

- WeilConjectures.primitiveCounitTensorRealization:
  lem-pur-primitive-counit-tensor-realization.
- WeilConjectures.primitiveCounitPullbackRealization:
  lem-pur-primitive-counit-pullback-realization.

No sorry remains in the item or its model definitions. This is a decomposition,
not a net hole reduction: two holes closed, two added, net zero.
The two lower statements assert no counit effectivity, beta invertibility,
inverse formulas, beta naturality or projection naturality.

Validation: all six packet modules and all 12 unchanged direct importers compiled
successfully in one server batch, in import order against the changed item, with
no errors or warnings. The six packet modules took 33.9--49.0 seconds each in that
batch. Temporary consumer source copies were removed after verification; no
consumer changes are delivered.

## No longer needed

No mathematical module or node is withdrawn or claimed pruned. The old bare
assembly proof dependencies lem-coef-semilinear-derived-sections and
def-trf-integral-comparison-sequence-systems are replaced in the comparison
existence node's proof by the two realization nodes and normalized reconstruction.
They remain in the definition imports and below the realization subarguments.
All original public imports are retained. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The mirror changed during the session. An intermediate snapshot exposed a separate
PrimitiveCounitEvaluation module and a unit-normalized Roos helper, but both were
absent when the consumer batch ran; the mirror again contained the two-hole item.
The final packet therefore supplies the evaluation module itself, relocating its
existing declarations and proved bodies unchanged. It also supplies the full
canonical Roos construction with the additional unit equation. Neither result is
assumed to be published. The existing evaluation existence and uniqueness nodes
point to their actual new source file.

The comparison-existence node's former single sentence cited only evaluation,
semilinear sections and sequence inverse image; those declarations do not directly
supply the normalized tensor and geometric realization isomorphisms. The new nodes
isolate precisely the strict-quotient and normalized-descent arguments already
written in steps 1--3 of the parent proof. The existing reconstruction theorem is
used as a generic counit-effectivity tool on arbitrary normalized systems; no unit
route is bypassed. The associated unit has no realized proof steps to replace.

## New nodes

lem-pur-coefficient-tower-roos-unit-normalization is proved. It retains the defining
inclusion/unit equation of the existing canonical comparison construction, alongside
its projection formula. This is necessary because projection equations alone do not
imply equality of morphisms in a derived inverse limit. Its new module imports the
existing canonical comparison proof privately to reuse normalizedRoosIso.

lem-pur-primitive-counit-tensor-realization supplies the tensor realization with
TensorModel. It follows the strict quotient-system tensor and normalized Roos
descent in Stacks 0941 and the existing two declared model/descent nodes.

lem-pur-primitive-counit-pullback-realization supplies the geometric realization
with PullModel. It follows the strict quotient inverse-image tower, the canonical
unit-normalized evaluation comparison and the same Roos localization descent.

Both were checked against zero complexes, empty schemes and first quotient level;
the pullback statement includes identity morphisms. Independent site and
coefficient universes are retained. Logged LeanSearch, Loogle, LeanFinder and
Mathlib grep searches found generic adjunction/derived-functor infrastructure,
not these normalized quotient-model statements. Blueprint searches for Roos and
primitive found no matching blueprint declaration to reuse.

Adjacent interface checked: primitiveQuotientPullbackModelExistence gives an
IntegralComparisonPullbackModel for a full CoefficientDerivedSystemCalculus and
IntegralComparisonRoosModel, with normalization on whole-system adjunction-coherent
presentations. The item instead quantifies over CoefficientDerivedSystemReduction
and PrimitiveCounit.RoosRealization and asks for the specific finite-component
PullModel equation. These are different interfaces; using the adjacent theorem
requires transporting the left adjoint, its finite comparison normalization and
the Roos datum and translating its strict generator equation. This conversion is
part of the pullback realization subargument, not an already available one-line
application. The adjacent universal-presentation theorem's disputed older form is
not imported or used.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
