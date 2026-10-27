## What changed

Extracted the existing public interfaces verbatim into
Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarData, publicly re-exported by
the item. Proved scalar identity unit normalization by adjunction uniqueness and
left-derived uniqueness, including its exact cochain representative equation.
Proved the computed and extended clauses from existing scalar normalization,
ringed-topos K-flat pullback, and clopen flat/K-flat detection. The main theorem
now assembles these with the separately stated comparison-descent and coherence
results. Change record: coord/changes/P8-clopen-derived-scalar-compositor.md.

## Proved and sorry left

Closed the original body of
AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_derived_scalar_compositor by
explicit existential and conjunction assembly. This is a decomposition, not a
net proof: one original hole closed, two holes added, net minus one.

Fully proved new results:
AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_unit_normalization
(node lem-pur-clopen-scalar-unit-normalization), and
AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_model_properties
(node lem-pur-clopen-scalar-model-properties).

Remaining sorry declarations:
AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_comparison_descent
(node lem-pur-clopen-scalar-comparison-descent), and
AlgebraicGeometry.Scheme.ProEt.ClopenScalar.clopen_scalar_comparison_coherence
(node lem-pur-clopen-scalar-comparison-coherence).
Each is a public theorem in its own module, with its exact statement, source and
complete proof in words. No definition or private helper contains sorry.

## No longer needed

No mathematical dependency or module has been pruned. The original theorem's
private KFlatRingedToposPullback import moves to its actual proof consumer
(ProEtaleClopenDerivedScalarModels). The private
SiteDerivedTensorDescentIndependentCoefficients and localization imports are dropped:
the interface definitions do not use them, and the two `sorry` statement modules
(comparison descent and coherence) do not need them for their statements; whoever
proves them imports the tensor-descent module then (reviewer correction). The scalar
normalization, clopen model detection and localization routes are retained.
No source-library declaration is removed or altered.

## Where the brief, the DAG or earlier work was wrong

The plan's ordinary same-coefficient tensor comparison does not directly give the
new-coefficient linear square. A direct sheafification-unit proof is needed (the
sectionwise tensor-presheaf maps are equal by their pure-tensor characterization).
The universe arguments of isKFlat_ringedToposPullback must be explicit for the
independent coefficient universe. Compiler transparency around the standard
derived category and chosen tensor restriction maps required explicit APIs.
No statement was found false; no target signature changes.

## New nodes

- def-pur-clopen-derived-scalar-comparison-data: extracted unchanged public interfaces.
- lem-pur-clopen-scalar-unit-normalization: multiplication units and their exact
  derived representative, fully proved.
- lem-pur-clopen-scalar-model-properties: computation isomorphisms and preservation
  of flat-term K-flat models over the new ring, fully proved.
- lem-pur-clopen-scalar-comparison-descent: ordinary and chain comparison, normalized
  derived lift and uniqueness; remaining proof obligation.
- lem-pur-clopen-scalar-comparison-coherence: composition and identity equations for
  an already normalized comparison; remaining proof obligation.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer correction (cc review, 2026-10-24)

Removed the unused private import
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients` from
ProEtaleClopenScalarComparisonDescent and ProEtaleClopenScalarComparisonCoherence
(their bodies are `sorry`; the statements use only the data module). The
`## Second reading by P8` above is not a reading; the independent review replaces it.

