## What changed

Proved `AlgebraicGeometry.stableUnderGeneralization_section_component_of_flat_of_geometricallyReduced_fibers`
in `Sheaf.AlgebraicGeometry.FlatReducedSectionComponentGeneralization`, with its statement
and public imports unchanged. The proof follows the current four-step DAG plan: lift the
specialization to the affine open base change, pass to the flat Noetherian model, handle
equal model images, and otherwise use the specialization trait and two-section generic
component theorem. The two component inverse-image equalities return membership to the
original general point. Cartesianness explicitly identifies the model's distinguished
geometric fibre. Updated the proof docstring to describe this assembly.

The three proof imports are the modules of the current declared proof dependencies:
`FlatPointedNoetherianComponentModel`, `FlatReducedSpecializationTraitData`, and
`FlatTraitTwoSectionConnectedOpen`. Their public Mathlib dependencies provide
the open immersion and its range used to lift the original points and specialization.
No definitions, signatures, shared modules, or unit routes were changed. No new nodes.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.stableUnderGeneralization_section_component_of_flat_of_geometricallyReduced_fibers`
(node `lem-trf-flat-reduced-section-component-generalization`). One of one holes closed;
zero holes remain in the item; zero holes added or split off. This is a proof from the
three already declared DAG dependencies, whose existing proofs may still contain sorry.
Validation: remote single-file compile passed without warnings in 4.5 seconds.
The theorem statement and all public imports were checked byte-for-byte against the
shared source; every line of the Lean module is within 100 characters. The delivery
tool runs the remaining preflight and axiom checks.

## No longer needed

Removed the following direct proof imports, replacing the obsolete low-level import plan
with the current three-helper DAG assembly:

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `WeilConjectures.Mathlib.Topology.NoetherianSpace`
- `Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`
- `WeilConjectures.AlgebraicGeometry.SectionComponentPullback`
- `WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation`
- `WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait`
- `WeilConjectures.AlgebraicGeometry.ConnectedGenericFibreTrait`

These low-level modules and nodes remain dependencies of the three helper lemmas where
needed; no whole module or DAG node is claimed globally pruned. All three current
`proof_deps` are used, so the existing node's route already matches the Lean proof and
needs no change. The source-library declarations and imports are untouched.

## Where the brief, the DAG or earlier work was wrong

The item's original imports and eight-step proof docstring predated the current reviewed
DAG split. The DAG now supplies exactly the three geometric reductions needed, all with
Lean declarations. The new proof uses these declarations rather than repeating the
underlying descent and trait geometry. Searches found no Mathlib theorem for the full
relative section-component generalization statement; the existing smooth variant has
stronger hypotheses and cannot prove this statement.

The equality case for model images, the specialization direction, the open-immersion
reflection of specialization, and the residue-field point in the reducedness hypothesis
are handled explicitly. The theorem also covers an empty source vacuously and coincident
original points through the equality branch.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
