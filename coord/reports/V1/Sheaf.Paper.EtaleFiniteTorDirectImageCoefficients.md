## What changed

Proved `AlgebraicGeometry.Etale.finiteTor_directImage_coefficients` in its existing
module, preserving the full statement and all public imports. Three proved private
helpers establish the coefficient annihilator, extract cohomology bounds from bounded
constructibility, and apply the existing etale scalar-flat-model theorem.

The proof uses the existing source-library module-valued relative cohomological-dimension
bound directly. Constructibility and the precise Tor window come from the existing
finite-type direct-image and residue-window declarations. The finite-constant projection
component and the proved scalar-mate invertibility helper are accessed by proof-only
`import all`; no dependency module is edited. A typed projection-isomorphism instance and local irreducibility of `scalarMate` and
`rightDerivedLowerStarProjectionMap` keep the final application from unfolding the
chosen functor constructions. The normalization is the existing
`scalarMate_restrict_eq_projection` equality with explicit bounded-below witnesses.

Change record: `coord/changes/V1-etale-finite-tor-direct-image-proof-context.md`.
The downstream check found no current Lean importers or external textual users.

Updated the item's node proof to this assembly. The unit's realized statement and steps
are preserved; this is an input to the same purity transport route.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.finiteTor_directImage_coefficients`
(node `lem-pur-etale-finite-tor-direct-image-coefficients`).

Server file compilation succeeded with the complete proof (15.2 seconds).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean file.
The existing imported statements `exists_etaleScalarFlatModel` and
`hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound` are separate existing proof jobs;
this delivery proves the assigned assembly from them, without claiming their completion.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`

The finite-constant projection module remains imported with `import all`, to use its
already-proved component lemma. The new proof imports the two existing modules
`Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow` and
`Sheaf.AlgebraicGeometry.EtaleScalarFlatModel`, which carry the current node's Steps 3
and 4. `Sheaf.Paper.FiniteCoefficientDirectImage` supplies its proved scalar-mate helper;
`WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude` supplies the existing
module-valued cohomological-dimension interface. Mathlib imports supply coefficient
unit arithmetic, finite presentation and Noetherianity.

No direct use of `def-kun-cd` is required: the existing source theorem gives the module
bound itself. The restriction comparison remains needed for the scalar mate. The
following old expanded-plan approvals are removed from the node's top-level `tool_uses`:

- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-module-direct-image-left-exact`
- `thm-sp-truncation-e2`
- `lem-exc-residue-tor-test`
- `lem-pur-derived-change-of-rings`
- `det-pe-finite-tor-comparison-noetherian`
- `det-sp-scalar-extension-functor`
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`
- `lem-weil-pbc-derived-scalar-extension-local-systems`
- `sk-prop-sf-comparison`

Their direct work here is carried by the existing residue-window and scalar-flat-model
statements. Some remain transitive dependencies of those statements or other modules;
no global unreachability or module withdrawal is claimed. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original Lean docstring and imports described the earlier eight-step plan, while
the current reviewed node has already extracted the residue-window input and assigned
scalar preservation to the existing flat-model theorem. The proof follows that current
five-step node. The relative vanishing theorem already exists for module sheaves over
an arbitrary field, so a fresh abelian-sheaf comparison is unnecessary here.

No statement or definition is changed. In particular finite B need not be flat, the
base field need not be separably closed, and the morphism need not be separated.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
