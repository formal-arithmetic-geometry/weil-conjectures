## What changed

Moved the unchanged normalized model definitions, `AdicLisseCalculusModels` and
`adicCalculusTensor` from `Sheaf.Paper.AdicLisseCohomologyCalculus` to the new shared data
module `Sheaf.Paper.AdicLisseCalculusData`. (Reviewer correction: the theorem's own
structure `AdicLisseCohomologyCalculus` stays unchanged in the theorem module and in the
theorem node's `lean.declarations`; the definition node does not own it.) The original module publicly reexports them. All
existing public declaration names, signatures, attributes and definition bodies are
preserved. This is needed to state independent comparison lemmas without an import cycle.
The change record is `coord/changes/A6-adic-lisse-calculus-data.md`.

The original existence theorem now assembles three independent source calculations:
normalized models; exact lisse tensor and ordinary fibre; and lisse linear duality with
its completed derived-Hom realization. The assembly derives the displayed cohomological
fibre comparison by whiskering and composing natural isomorphisms. The component equation
is definitional. All object and map data remain the specified original constructions.

Validation: the five-file delivery set compiled in import order with no warnings.
The unchanged original item also compiled before editing. A byte comparison confirms
that every moved definition and both structures are unchanged, including their docstrings.
All changed Lean files have lines of at most 100 characters; the node proof-dependency
lists equal the unions of their proof-step uses. All five unchanged downstream
consumers compiled against the revised modules: `NormalizedClassicalWeilRealization`,
`TateTwistSupportCondition`, `AnchoredPureCurveCriterion`,
`ClassicalWeilFiltrationHeartTransport`, and `GeometricQuotientWeilCompositionSeries`.
Their temporary source copies were removed from the packet after submission of the
validation compile; no consumer adaptation is needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adic_lisse_cohomology_calculus`
(node `lem-per-adic-lisse-cohomology-calculus`), by a complete categorical assembly.
The private helper `induced_tensor_fiber` is proved and gives both the natural
isomorphism and its required component equation.

Added exactly three holes, each the entire proof of one public theorem:

- `AlgebraicGeometry.Scheme.adic_lisse_normalized_models`
  (`lem-per-adic-lisse-normalized-models`): the normalized model bundle only.
- `AlgebraicGeometry.Scheme.adic_lisse_exact_tensor_comparisons`
  (`lem-per-adic-lisse-exact-tensor-comparisons`): the two tensor comparisons only,
  for any already supplied normalized models.
- `AlgebraicGeometry.Scheme.adic_lisse_linear_dual_comparisons`
  (`lem-per-adic-lisse-linear-dual-comparisons`): the independent duality calculation,
  for already supplied normalized models, without any tensor/cohomology assertion.

There are zero holes in the item module and zero in the shared data module.
This is a decomposition: one hole closed, three added, net minus two; it is not a
claim to have proved the geometric comparison results. The split statements are
strict parts of the original argument, with distinct conclusions and source proofs.

The required delivery command has three times returned exit 75 after its full 50-minute
priority-slot wait (`DELIVERY BUSY: 6 deliveries are running on this machine`).
Each attempt waited the full 50 minutes. No packet checks or push occurred in those attempts. Compilation and downstream
validation above are complete.

## No longer needed

The original public imports move to the shared data module and remain reexported.
The item module needs only its public data import and the three private proof imports.
The following original private imports are removed from the item:

- `Sheaf.Paper.LocalizedTStructure`
- `Sheaf.Paper.GaloisLisseRepresentations`
- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.Kernels`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.Paper.LisseModuleSheaves`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.Paper.LisseAdicSheaves`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist`
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
- `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
- `WeilConjectures.Mathlib.Topology.NoetherianSpace`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.KoszulReconstruction`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.IntegralTensorProduct`
- `Sheaf.Paper.IntrinsicQbarCategory`
- `Sheaf.Paper.LisseCompletedSystemComparison`
- `Sheaf.Paper.LisseIntegralSmallCoefficients`
- `Sheaf.Paper.SfCommonStageWeilCohomology`

The source results used by the three new proof plans remain needed there; this delivery
does not claim that their DAG nodes have become unnecessary. No blueprint unit or unit
proof step is bypassed. No source-library module or declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The proof plan gives the mathematical finite-stage calculations, but no existing
declaration supplies the fully normalized global model bundle or the simultaneous
natural tensor and dual comparisons at its exact endpoints. Existing representation,
completed-system, localized t-structure and scalar-operation results are lower-level
interfaces; the new nodes record the three remaining source calculations explicitly.
The `FdIntegralIdentityRationalEquivalence`, `FdCompletionInverseScalarCoherence`
and `FdCommonStageComparisonDescent` interfaces provide reusable stage-equivalence
and coherence machinery, but do not supply the lisse realization, standard
cohomology and completed-point fibre bundle with this item's normalizations.

The rework row records an earlier quarantine caused by an unavailable import. The
current live item exists and compiles unchanged; its data and both Lean attachments
are preserved, with the data attachment relocated to the shared data module.
There is no withdrawal and no target statement change.

## New nodes

`lem-per-adic-lisse-normalized-models`: BS 6.8.4, 6.8.11 and 6.8.14 give realization,
standard cohomology and completed point-section fibres normalized at each finite field.

`lem-per-adic-lisse-exact-tensor-comparisons`: BS 6.8.4 and 6.8.15, together with the
recorded complete-tensor reconstruction, give exact tensor and ordinary fibre comparison.
This result excludes the independently derived cohomological-fibre composition.

`lem-per-adic-lisse-linear-dual-comparisons`: finite-free dual systems and exact Hom
identify the lisse dual with the completed coefficient derived dual. It does not include
the tensor/cohomology comparison.

Definition relocation record: `coord/changes/A6-adic-lisse-calculus-data.md`.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
