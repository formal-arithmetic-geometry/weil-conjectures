## What changed

Proved every affine clause of
`AlgebraicGeometry.SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing`
from the actual homogeneous localizations and existing twisting sheaf. Private helpers
construct the multiplication-by-e linear equivalence, identify its sections, evaluate
fractions in prime localizations, prove the coefficient and basic-open equations,
and prove transitions and the scalar cocycle. Symmetric-algebra induction proves
that the arbitrary degree-one generators cover. These arguments do not require
finite generation or nonzero denominators.

The global conclusion is reduced to three distinct source results: normalized
quotient descent, open-base comparison, and ordered free comparison. The assembly
also proves the degree-zero fraction restriction equation with `Away.map_mk`.
The theorem signature is unchanged. `AffineRestrictionFormulas` has an equivalent
implementation using the new structure `NormalizedAffineRestriction`: its fields are
exactly the old comparison isomorphism, chart equation, and degree-one-section equation.
The independent fraction restriction conjunct stays unchanged. The structure is
publicly imported because the predicate now uses it. No consumer names this predicate
outside the item’s theorem; the geometry parent discards that conjunct.
Local transparency attributes keep the relative-Proj and tensor-pullback constructions
shared while elaborating the comparison equations.
The draft follows X5’s landed move of the quotient data into
`ProjectiveBundleQuotientData`, preserving the definitions-only dependency. New proof
imports are the three modules below. No source-library file is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing`.
This is a decomposition, not a complete sorry-free proof: three holes are added.

- `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_normalized_quotient_with_affine_restriction`
  in `Sheaf.AlgebraicGeometry.SymmetricProjNormalizedDescent`, node
  `lem-trf-symmetric-proj-normalized-descent`.
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.open_compatibility_of_normalized_quotient`
  in `Sheaf.AlgebraicGeometry.SymmetricProjOpenComparison`, node
  `lem-trf-symmetric-proj-open-comparison`.
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.free_compatibility_of_normalized_quotient`
  in `Sheaf.AlgebraicGeometry.SymmetricProjFreeComparison`, node
  `lem-trf-symmetric-proj-free-comparison`.

Validation: all four modules compile cleanly through `lcompile.py --all`;
the item takes 37.1 seconds, with no warnings.

The item module contains zero sorry. All affine calculations and the final combination
are complete Lean proofs. Each retained theorem is a strict part of the original
argument: descent does not assert either global comparison or the affine formulas;
the two comparisons assume a normalized datum and establish different conclusions.
The comparison statements hold for any normalized datum, since its generator field
pins its frames and quotient. All include empty base, zero module, nilpotent generator,
and rank-one free module (r=0) cases without cancellation hypotheses.

## No longer needed

The following old private proof imports are removed from the item module:

- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.RingTheory.SymmetricAlgebraBaseChange`
- `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`

The affine proof uses the public twist and homogeneous-localization APIs directly,
so it does not need to construct a second associated graded-module sheaf or invoke
affine tilde, tensor-section, scalar-extension, or generic descent existence there.
The old global dependencies move to the corresponding new construction/comparison
nodes; they remain needed by that mathematics, so no entire old node or module is
claimed pruned from the targets. In particular, no upstream declaration is withdrawn.
The parent's proof_deps now records the three new results and the four direct affine
inputs. The old parent `tool_uses` entries removed are:
`lem-weil-pbc-symmetric-algebra-graded`,
`lem-weil-pbc-proj-graded-module-sheaf-exists`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-weil-pbc-symmetric-algebra-base-change`,
`lem-nagata-affine-proj-scalar-extension`,
`lem-weil-pbc-site-module-sheaf-gluing`,
`prop-nagata-relative-proj-functoriality`,
`lem-weil-pbc-affine-opens-basis`, and
`lemma-nagata-relative-proj-exists`. These inputs belong to the new global
construction/comparison proofs; none is claimed unnecessary there.

## Where the brief, the DAG or earlier work was wrong

The existing declarations for associated graded-module sheaves and generic gluing do
not themselves state descent for the actual `Proj.twist` with its specified section
normalization. Likewise relative Proj functoriality alone gives no twist comparison.
Those specialization and normalization arguments are genuine remaining work, now
isolated rather than hidden in an application of a generic theorem. The parent
`projective_bundle_quotient_geometry` cannot be used as a shortcut: its DAG and its now-proved Lean body
already depend on this item.

No mathematical statement is disputed. No target, theorem signature, source-library declaration, or unit route has been weakened.
The restriction-predicate implementation changes only its packaging, preserving every equation.

## New nodes

`lem-trf-symmetric-proj-normalized-descent` isolates Stacks Tags 01NR/01OB/01MS,
original steps 1--8 and the empty-chart check. Its conclusion specifies the existing
normalized quotient and chart-compatible affine restrictions on all degree-one sections.

`lem-trf-symmetric-proj-open-comparison` isolates the arbitrary-open part of the
relative Proj base-change construction, original step 9. It uses normalized descent
over the open and chart uniqueness for the scheme and line comparisons.

`lem-trf-symmetric-proj-free-comparison` isolates Tag 01OE, original step 10, including
both projective-space realizations, every ordered basis, and the full affine polynomial
normalization required by `AffineFreeComparison`.

Each node inherits the chapter, unit and historical blueprint ancestor, records all
three required kinds of Mathlib search, and carries the source proof in words in both
its node and Lean docstring. The local proof-elaboration attributes are recorded in
`coord/changes/J2-symmetric-proj-chart-elaboration.md`. The equivalent restriction-predicate refactor is recorded there as well, with the
verbatim old and new definitions and the consumer audit.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
