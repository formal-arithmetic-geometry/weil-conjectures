## What changed

Wrote the proof of
`AlgebraicGeometry.isAffineOpen_spec_of_isNoetherianRing_of_topologicalKrullDim_le_one`
in `Sheaf.AlgebraicGeometry.NoetherianAffineDimOneOpen` along Stacks 09N9.
Noetherian stalks and compactness are supplied by Mathlib; the stalk
Krull dimension is its coheight, bounded by the dimension of the spectrum.
Apply the stated positive higher-direct-image vanishing, qcqs quasi-coherent
pushforward, affine cohomology vanishing, and the stated Leray equivalence.
The existing source-comparison equivalence transfers H¹-vanishing to module
cohomology for Serre's criterion. The signature is unchanged, including the
empty open and zero ring. No definitions or public imports changed.
The open's compact-space instance is explicit, as is enough injectives for its
module category, supplied by the existing ringed-space theorem.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isAffineOpen_spec_of_isNoetherianRing_of_topologicalKrullDim_le_one`
(node `lem-a1-affine-curve-open-affine`). Added no holes. No sorry remains in
the delivered module. The proof uses the existing theorem
`AlgebraicGeometry.isZero_higherDirectImage_open_of_stalk_dimension_le_one`,
which is still sorry in its own module; that is an existing dependency, not
an added hole.

Validation: the resumed single-file compiler run passed cleanly (11.3 seconds).
The resumed run supplied the explicit compact-space and enough-injectives
instances required by Lean. Final preflight is recorded by the delivery tool.

## No longer needed

Removed proof-only imports:
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.StructureSheaf`,
`Mathlib.AlgebraicGeometry.FunctionField`,
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Mathlib.Topology.NoetherianSpace`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.AlgebraicGeometry.OpenImmersion`, and
`Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`.
The Mathlib imports are redundant with the retained Noetherian, Properties,
quasi-coherent pushforward and Krull-dimension APIs.
The proof does not use the separate function-field clause.
The final import's node `pqf-lem-affine-vanishing` is replaced by the already
proved source affine-scheme theorem `lem-pc-affine-vanishing`; this avoids
an unnecessary conversion through cohomology on the top open. Its obsolete
top-level `tool_uses` approval was removed. Added proof-only imports for
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`,
`WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison`, and
`WeilConjectures.Mathlib.Topology.KrullDimension`.
All other declared mathematical dependencies remain used, directly or through
the Mathlib instances implementing the local Noetherian and compactness steps.
No unit-level route changes and no new nodes.
The existing
`isAffine_of_isOpenImmersion_of_topologicalKrullDim_le_one` was also checked:
it requires irreducibility and a nonempty source, so does not supply this
general statement. The Dedekind-domain theorem requires integrality and
regularity, which are likewise absent here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error. The planned affine-open vanishing interface and the
Leray interface use different cohomology presentations. Using the existing
source affine-vanishing theorem and module-cohomology source comparison gives
the same Stacks argument with a shorter formal bridge. The node proof and
proof dependencies have been updated to match.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
