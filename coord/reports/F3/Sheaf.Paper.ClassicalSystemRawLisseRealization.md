## What changed

Replaced the single hole in `Sheaf.Paper.ClassicalSystemRawLisseRealization` with a
complete assembly from existing realization theorems and four strictly smaller named
comparison steps. Added one module and one DAG node for each remaining step.

The parent proves `modulesFullyFaithful`, `scalarCoherence`, `restrictionCoherence`, and
`mixedComparison` as private helpers. Full faithfulness of the ordinary finite module
realization follows by composing the raw Hom bijections, full heart inclusion, and
lisse sheaf realization bijections, then transporting along the specified comparison.
Scalar units/associators, restriction units/compositors, and the mixed comparison are
lifted through fully faithful functor-category whiskering. Their required equations
are exactly `map_preimage`. The restricted identified-fibre isomorphism is explicitly
the inverse completed comparison, the fibre image of the supplied isomorphism, and the
finite classical fibre comparison. Existing point, pullback and field normalization
witnesses are retained from `lisse_rational_realization`.

The four new statements cover distinct pieces of the original argument: finite objects
and point comparisons (steps 1-5,8-9), actual finite operations (step 6), common-stage
descent (step 7), and intrinsic completed fibre pullback (step 9). None is the original
statement under another name. The unit route is unchanged. Zero rank, empty bases,
ramified exponents (including e=1 and e=2), arbitrary coefficient inclusions, prescribed
isomorphisms, and independent scheme/algebraic-closure universes were checked in prose.

Change record: `coord/changes/F3-classical-raw-lisse-decomposition.md`.

## Proved and sorry left

Closed the original direct hole:
`WeilConjectures.ClassicalRawLisse.classical_system_raw_lisse_realization`
(node `lem-zl-classical-system-raw-lisse-realization`). The item has zero remaining direct
holes. This is a decomposition, not a sorry-free proof of the mathematics: one upper
hole is replaced by four lower holes, a net increase of three direct holes.

The delivery adds exactly these four named public holes:

- `WeilConjectures.ClassicalRawLisse.classical_raw_lisse_finite_construction`
  (`lem-zl-classical-raw-lisse-finite-construction`).
- `WeilConjectures.ClassicalRawLisse.classical_raw_lisse_finite_operations`
  (`lem-zl-classical-raw-lisse-finite-operations`).
- `WeilConjectures.ClassicalRawLisse.classical_raw_lisse_intrinsic_fibre_pullback`
  (`lem-zl-classical-raw-lisse-intrinsic-fibre-pullback`).
- `WeilConjectures.ClassicalRawLisse.classical_raw_lisse_common_descent`
  (`lem-zl-classical-raw-lisse-common-descent`).

Every new hole is the entire proof of its theorem. No definition contains a hole.
The four private categorical helpers and the theorem assembly contain no direct sorry.
Compilation and delivery-preflight results are recorded by the delivery tool.
The coherence lifts explicitly name both source functors when applying `map_preimage`.
Local irreducibility of the completed pullback and scalar-extension definitions prevents
expensive unfolding during these categorical comparisons; no exported definition changes.

## No longer needed

Removed these redundant direct proof imports from the parent:
`Sheaf.Paper.RationalLocallyFree`, `Sheaf.Paper.SfConstructibleHeart`,
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
`Sheaf.Paper.RationalCoefficientCategoryComparison`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
`Sheaf.Paper.AdicHeartIntrinsicFibres`, `Sheaf.Paper.ContinuousRationalDerivedRealization`,
`Sheaf.Paper.LisseCompletedSystemComparison`, `Sheaf.Paper.LisseRationalRealization`,
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`,
`Sheaf.Paper.LisseIntegralSmallCoefficients`.
Their required interfaces remain available through the unchanged public prerequisites.
The new finite-construction module also omits the unused direct import
`Sheaf.Paper.LisseFieldNormalization`; its statement only uses point and pullback data.
The geometric and coefficient arguments themselves remain needed by the four new
steps; they are moved dependencies, not mathematical pruning. No module is withdrawn,
no declaration is removed, and no original mathematical dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The prose plan correctly describes the mathematical route but understates the amount
of Lean interface transport: the completed-system comparison uses a larger coefficient
universe, while the classical family uses small coefficients; the PBC and intrinsic sf
fibre presentations also require explicit normalized transport. The original theorem
alone does not supply these bridges as directly applicable declarations. They are now
separate statements with sources, proof plans, and Lean signatures.

The original route and theorem signature remain unchanged. The existing normalized
lisse theorem already provides the last three normalization clauses, so these are
reused directly. Coherence requires no additional geometric theorem once the finite
comparisons exist; fully faithful lifting proves it.

## New nodes

`lem-zl-classical-raw-lisse-finite-construction`: the quotient/limit-normalized integral
comparison, degree-zero raw realization, ordinary sf/PBC comparison and point data.
It carries the finite construction and point portions of the original proof.

`lem-zl-classical-raw-lisse-finite-operations`: actual finite-level scalar and restriction
operations, completion-cone units, raw fraction formulas and prescribed comparison maps.
It assumes the finite realization and asserts no common-stage data or coherence.

`lem-zl-classical-raw-lisse-intrinsic-fibre-pullback`: the intrinsic natural isomorphism
for completed pullback followed by adic fibre. It has no classical realization input;
the parent constructs the comparison for a supplied identified restriction from it.

`lem-zl-classical-raw-lisse-common-descent`: the common-stage realization, fibres and
restriction descent, assuming all finite data and their proved coherence. It supplies
neither finite realization nor finite operations.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
