## What changed

Replaced the single partial proof in
`Algebra.ActiveRootNormalization.activeRootTower_normalization_splitting` by a complete
Lean reduction combining finite-stage descent, regularity of the selected root stage,
ind-etaleness of the prescribed strict-local algebra, puncture integral closedness, and
restriction of the splitting to the actual normalization. The theorem's full signature
and structural-map equations are unchanged.

Proved the private helper `unit_of_not_mem_geometricPoint`: transfer the local-ring
structure along the specified spectrum isomorphism, transport the closed-point equation
through the small-to-full strict-henselization comparison, and use the maximal-ideal
criterion for units. Apply it to every inactive parameter.

Used `Algebra.flat_root_tower_nonzerodivisor` with the identity flat maps and all positive
orders to prove the necessary regularity on C_m. Used
`Scheme.smallStrictHenselization_indEtale_of_affine_chart` on the identity affine chart
to prove ind-etaleness for the actual small-colimit presentation in the statement.

Relocated the 22 unchanged structural constructors into the new public support module
`Sheaf.RingTheory.ActiveRootNormalizationData` to avoid a cycle between the three new
statement modules and the original theorem. The item publicly imports the data module.
The change record is `coord/changes/active-root-normalization-data-relocation.md`.
There are zero current direct Lean importers to adapt or compile. The DAG parent
`lem-sfb-snc-tame-root-etale-extension` and its dependency are preserved.

Added three separate modules with named intermediate statements and complete sourced
proof sketches. None is a renamed copy of the original theorem: descent has no normality
or geometry; puncture integral closedness has no D or splitting; fixed-stage restriction
has no infinite splitting or geometric point, and assumes the separately established
puncture characterization and injectivity.

## Proved and sorry left

Original module: 1 hole before, 0 holes after. The body of
`Algebra.ActiveRootNormalization.activeRootTower_normalization_splitting` is a checked
proof from the following three new intermediate statements. This is a decomposition,
not an independent proof of the original theorem. Independently closed original holes: 0.
New holes: 3. Net hole change of this packet: +2.

Every remaining hole is the whole proof `:= by sorry` of its named public theorem:

- `Algebra.ActiveRootNormalization.activeRootTower_specified_splitting_descends`
  (`lem-sfb-active-root-specified-splitting-descent`).
- `Algebra.ActiveRootNormalization.rootStage_puncture_indEtale_integralClosure`
  (`lem-sfb-root-stage-puncture-ind-etale-integral-closure`).
- `Algebra.ActiveRootNormalization.activeRootStage_normalization_restriction`
  (`lem-sfb-active-root-stage-normalization-restriction`).

The data module and the original module have zero holes. The private unit helper is
proved. No data definition depends on an unproved existence theorem. The three
remaining steps have no new hypothesis on the original theorem: the assembly supplies
every premise, including injectivity of the puncture required to lift product coordinates.

Edge-case audit: r=0 uses the already proved empty-family clause implicit in the root-stage
regularity theorem; active may be empty; d=0 is explicitly retained in the finite product
presentation and integral-product argument; the new general algebraic lemmas allow zero
rings. A geometric point excludes the zero B case of the original theorem. The descent
lemma even permits p=0 or p=1: order 1 remains an initial object and products preserve
coprimality. All maps are the prescribed maps, not arbitrary isomorphisms.

Validation: remote compilation of the support modules and original proof, followed by
`deliver3.py` compilation and preflight. Detailed results appear in the delivery output.

## No longer needed

Removed the original proof-only imports:
`Sheaf.RingTheory.ColimitCategoryFpAlgebras`,
`WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale`,
`WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`,
`WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`, and
`Sheaf.RingTheory.IntegralClosureIndEtaleBaseChange`. Their mathematics is retained where
needed in the smaller steps, or through the small-model chart wrapper; this does not
claim those modules are globally unused.

Removed the public import `Sheaf.RingTheory.StrictHenselizationPresentationIn`; that
separate local-base presentation structure is not used by this geometric-colimit proof.
Other construction imports moved to the data module and remain publicly available.

The direct proof dependency `lem-sfb-monic-quotient-faithful-tensor-coordinates`
(`Sheaf.RingTheory.MonicQuotientFaithfulTensorCoordinates`) is no longer needed on this
branch. The already proved `lem-sfb-flat-root-tower-nonzerodivisor` provides its required
finite-stage regularity conclusion without that unfinished coordinate theorem.
No module is withdrawn, and no claim is made that other branches do not use it.
The proof-only citation `def-weil-pbc-finite-etale-category` is also unnecessary:
the Lean conclusion ends with the actual algebra isomorphism, so the old final
"take spectra" explanation requires no further theorem in this module. Its original
statement-dependency entry is preserved. The other original proof dependencies remain
in the intermediate-node plans instead of being duplicated in the assembly node.
The new statement modules import only their public statement dependencies; the modules
for their future proof plans are not imported while their proofs remain holes.

## Where the brief, the DAG or earlier work was wrong

The main statement has no identified mathematical error. Its old proof import of the
upstream affine-chart theorem uses `strictLocalization`, whereas the actual hypothesis
presents `strictHenselizationScheme`. The existing small-model chart wrapper supplies
the needed comparison; it is used explicitly.

The original DAG regularity step suggested proving an iterated monic quotient coordinate
argument again. The existing proved flat root-tower theorem already supplies exactly the
needed injection, so no coordinate-theorem hole is imported.

The original node's blueprint ancestor is null; `tools/blueprint_refs.py ancestor`
reports the same inherited null. The new nodes retain that ancestry and explicitly name
current blueprint clause (3), `det-thm-sf-ctf-stability-direct-images`, and the precise
parent steps. The unit route is unchanged. Blueprint searches for 'active root' and
'integral closure' found no duplicate of any of these three steps.

Generic tools outside the unit: the small-model affine-chart theorem, strict-henselization
local structure, backward closed-point equation and small-model structural comparison
supply the geometric input; the existing colimit finite-presentation, tensor-colimit,
normal-total-fraction and ind-etale integral-closure theorems are used by the smaller
steps. These are tools for the existing active-root argument, not alternate unit routes.

## New nodes

`def-sfb-active-root-normalization-pushout-data` records the unchanged 22 constructors
in `Sheaf.RingTheory.ActiveRootNormalizationData`. It adds no new mathematical notion
and no hole, and permits the proof-step modules to share the actual constructions.

`lem-sfb-active-root-specified-splitting-descent` records parent steps 1--3 in
`Sheaf.RingTheory.ActiveRootSpecifiedSplittingDescent`: descend the map and inverse,
then enforce both inverse equations, retaining agreement with the prescribed splitting.

`lem-sfb-root-stage-puncture-ind-etale-integral-closure` records the regular-stage,
normal-total-fractions and first 0CBF argument in
`Sheaf.RingTheory.RootStagePunctureIndEtaleIntegralClosure`. Regularity is a premise
supplied by the proved root-tower theorem, not part of this remaining hole.

`lem-sfb-active-root-stage-normalization-restriction` records fixed-stage root substitution,
scalar extension of the splitting, the second 0CBF comparison, and restriction by
coordinatewise integrality in `Sheaf.RingTheory.ActiveRootStageNormalizationRestriction`.
Its premises explicitly include both injectivity and the integral-closedness formula,
so the resulting epsilon is an isomorphism of the actual base-changed closure.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
