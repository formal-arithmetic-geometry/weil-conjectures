## What changed

Restored `lean/Sheaf/Paper/AdicSmoothDualizingComplexes.lean` from the quarantine
path named in rework.tsv. This is the assigned elaboration repair, with five
additional existing holes closed. The archived file failed at rationalIntegration
while inferring the type of its large composite. Explicit Hom result types and
irreducible attributes on integralCounitAmbient, rationalIntegration and
closedIntegration avoid that inference and repeated unfolding. All three map
bodies are verbatim; a separate interface check proves HEq with the original
composites by unfolding the named maps and rfl. Local irreducibility of PurCompactSupport.image, sfIntrinsicModuleEquivalence
ProEtale.comparisonUpperStar, finiteEtaleTateTensorFamily and exactSingleShiftIso,
together with scoped transparency controls, makes
the unchanged finite-comparison definitions usable with the repaired interface.

Added private proof imports of
Sheaf.AlgebraicGeometry.FiniteEtaleTateTensorFamily and
WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers. All declaration signatures are preserved. Removed the unused public import
Sheaf.Paper.CommonStageCompactWeilCohomology: none of the item declarations uses
its cohomology definitions, and neither direct archived consumer refers to them.
No statement or compact-support functor was replaced. The existing DAG attachment,
unit route and pending dependencies are retained; its proof now records the
finite tensor-family preliminary actually used.

Validation: the initial repaired item compiled cleanly in 46.6 seconds (lcompile
result 364916e2a0203a3f0b8203da). A delivery-probe compile then exceeded 60 seconds;
local irreducibility of the site/scalar functors limits further unfolding. The
profiled revised item compiled in 55.8 seconds (48e8c60ae1a37818e479cdeb);
all profiling options were removed before delivery. Removing the unused public
cohomology import compiled cleanly in 49.3 seconds (23ad29663d4a449494938a37).
The final file also sets backward.isDefEq.respectTransparency.types false, which
separately compiled cleanly in 49.2 seconds before the import removal. The three original-body interface equalities compile cleanly
in 9.1 seconds (65e8219e6326a68ca4339fd5). The live and quarantined consumer audit
is recorded in coord/changes/A2-adic-smooth-dualizing-elaboration.md. No consumer
adaptation, source-library edit, new statement, or withdrawn module.

## Proved and sorry left

Closed 5 of the original 12 holes, added 0 holes, split off 0 statements.
All names below are in namespace WeilConjectures.AdicSmoothDualizing.

Proved:

- `existsUnique_etalePowerZero`.
- `existsUnique_etalePowerPositive`.
- `etalePowerFlat`.
- `finiteUnitPlus`.
- `structureIsOver`.

The flatness proof now rewrites the published tensor-family object equation
explicitly, so it does not unfold the signed-family construction.
The zero and positive-step proofs use uniqueness of the explicitly prescribed
isomorphism. Flatness follows from the existing tensor-family inverse. The finite
unit proof transports the bounded-below property of a degree-zero single complex.
The structure-map proof uses Hom.isOver_iff and Spec.map_id, retaining all original
section hypotheses.

Seven existing holes remain unchanged, each with its original source/proof
docstring and node cor-pur-adic-and-rational-smooth-dualizing-complexes:

- `existsUnique_lineProjection`.
- `existsUnique_etalePowerPresentation`.
- `existsUnique_rootComparison`.
- `existsUnique_finiteRealization`.
- `integralTwist_mem`.
- `existsUnique_integralIdentification`.
- `adic_and_rational_smooth_dualizing_complexes`.

This delivery completes the assigned definition/elaboration repair and is a
partial proof delivery, not a proof of the whole corollary. There are no added
sorrys in definitions or unnamed proof steps.

## No longer needed

Removed unused public import:

- Sheaf.Paper.CommonStageCompactWeilCohomology

Removed unused private imports:

- Sheaf.Paper.ConstantCoefficientObjectsConstructible
- WeilConjectures.EtaleCohomology.Purity.Smooth.Adic
- WeilConjectures.EtaleCohomology.Purity.Smooth.Rational
- WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction
- WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization
- Sheaf.Paper.ConstantCoefficientScalarNormalization
- Sheaf.Paper.DerivedPullbackTensorHom
- Sheaf.Paper.FiniteTorAmplitudeSites
- Sheaf.Paper.PurAdicReconstruction

These imports were unused by the restored definitions and the five completed
proofs. No mathematical DAG dependency or module is withdrawn: reconstruction,
coefficient naturality, and trace coherence are still needed by the remaining
holes. In particular zero live importers of the quarantined item is not treated
as evidence that its mathematics is unused. All adopted source declarations stay.

## Where the brief, the DAG or earlier work was wrong

The archived module is not usable unchanged: rationalIntegration's inferred type
traverses a large composite and hit the deterministic heartbeat limit recorded
in rework.tsv. Stating the existing Hom types explicitly and controlling reduction
repairs this without changing the maps. The final corollary remains unproved in
this packet. No disputed mathematical statement was encountered, no new nodes
were created, and no target statement changed.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
