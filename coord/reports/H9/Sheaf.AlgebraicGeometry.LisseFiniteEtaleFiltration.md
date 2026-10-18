## What changed

Proved `AlgebraicGeometry.Etale.exists_lisse_finiteEtale_filtration` with its exact existing
signature. The proof constructs the Noetherian component partition, a finite monodromy
torsor and Sylow quotient, an exact associated-module functor, the scalar-span filtration,
actual Subobjects and categorical cokernels, and a finite coproduct cover with an explicit
constant geometric fibre count. Empty bases, zero modules and zero coefficient rings are
included. The proper-base-change unit's route is retained; only this auxiliary argument
changes.

The new `Sheaf.AlgebraicGeometry.FiniteRingTorsorAssociatedModule` constructs the
associated module functor for an arbitrary commutative coefficient ring. It reuses the
existing torsor spaces, actions and restrictions; the old prime-coefficient API is unchanged.
Two further new modules prove its pullback/unit comparisons and recovery of a
module sheaf trivialized by the torsor. The comparisons reuse the existing private
graph-splitting helpers through a proof-only `import all`; only the evaluation arguments
that depend on generic coefficients are supplied here. Linearity follows from
module-valued locally constant coordinates. The associated functor and section representation are real
constructions, with no data chosen from an unproved mere existence theorem.

Validation: all four delivery modules compile. The delivery preflight also checks the
axioms of every declaration. No existing source-library definition or consumer is edited.

## Proved and sorry left

Closed one of the original one holes:
`AlgebraicGeometry.Etale.exists_lisse_finiteEtale_filtration`.
Added zero holes; split off zero unproved statements. No `sorry` remains in any delivered
Lean file. Both new theorems, `associatedModuleFunctorOver_comparisons` and
`exists_finiteRing_module_descent`, are fully proved; the new construction has zero holes.
This is a proof, not a decomposition into unproved obligations.

## No longer needed

Repair: removed the copied `graphCoproduct_isIso`, `graphHomeo`, `graphHomeo_mk`,
`sectionAction_mul`, `sectionAction_one`, and `graphHomeo_action` declarations from
`FiniteRingTorsorModuleComparisons`. The proof uses the originals in
`WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective` via `import all`.
Also removed the now-unused direct import of
`WeilConjectures.Mathlib.CategoryTheory.Extensive` from the comparisons module.

Removed direct proof imports:

- `Sheaf.Paper.GaloisLisseRepresentations`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The proof uses a finite monodromy torsor and its subgroup quotient instead of constructing
a continuous fundamental-group representation and invoking a full Galois/lisse equivalence.
It counts fibres of the quotient and coproduct directly, so it needs no separate trace-degree
theorem. Mathlib connected components, closed-immersion affineness, and finite coproduct APIs
replace the longer irreducible-component/idempotent/localization and spectrum-product route.

Original declared proof dependencies no longer used directly (their modules should not be
re-imported merely to follow the superseded plan):

- `cor-galois-lisse-representations`
- `cor-galois-open-subgroups`
- `def-weil-finite-integral-morphism`
- `def-weil-irreducible-components`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-finite-affine-coproduct-spectrum`
- `lem-weil-pbc-finite-etale-trace-degree`
- `lem-weil-pbc-noetherian-finitely-many-components`
- `lem-weil-pbc-principal-localization-open-immersion`
- `lem-weil-pbc-spec-clopen-idempotent`
- `thm-galois-fundamental`

Removed obsolete top-level tool approvals, retaining the still-used affine, coproduct, composition and primary-filtration entries:

- `cor-galois-lisse-representations`
- `thm-galois-fundamental`
- `cor-galois-open-subgroups`
- `lem-weil-pbc-noetherian-finitely-many-components`
- `lem-weil-pbc-spec-clopen-idempotent`
- `lem-weil-pbc-principal-localization-open-immersion`
- `lem-weil-pbc-finite-etale-trace-degree`

Non-Mathlib modules removed from this item's import closure (this does not assert they
are globally unused by other targets):

- `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizerOpenIndex`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizerRange`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups`
- `Sheaf.CategoryTheory.EquivalenceInternalModule`
- `Sheaf.CategoryTheory.FiniteContinuousModule`
- `Sheaf.CategoryTheory.Galois.AbstractEquivalence`
- `Sheaf.CategoryTheory.Galois.AutProfinite`
- `Sheaf.CategoryTheory.Galois.CoproductMorphismComponents`
- `Sheaf.CategoryTheory.Galois.StacksGaloisAxioms`
- `Sheaf.CategoryTheory.Galois.StacksGaloisCategory`
- `Sheaf.CategoryTheory.Galois.StacksMonoComplement`
- `Sheaf.CategoryTheory.InternalModule`
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrCore`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrFactorization`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `Sheaf.NumberTheory.Padics.LatticeStabilizerOpen`
- `Sheaf.Paper.AdicTowerReconstruction`
- `Sheaf.Paper.GaloisLisseRepresentations`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseAdicSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
- `WeilConjectures.AlgebraicGeometry.FiberDegreeOfSplitCofan`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleDegreeSplitAt`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTrace`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegreeTrace`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDescent`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExists`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsExistence`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExistsUniqueness`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalSums`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalization`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalizationSectionFormula`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTracePullbackSum`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitComponent`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitCover`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitReindexing`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitSumCompatibility`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitting`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplittingPullback`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`
- `WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation`
- `WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian`
- `WeilConjectures.RepresentationTheory.DiscreteContinuousRep`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`

## Where the brief, the DAG or earlier work was wrong

Returned point repaired: the retained comparisons module copied five coefficient-independent
private theorems and their graph homeomorphism from the source module. `import all` makes
those existing helpers available directly, so all six copies have been removed. The node
now records this reuse. No source-library signature or visibility change is required.

No statement was false and no target was changed. The planned lisse correspondence is
unnecessarily broad for this argument. The existing finite torsor construction was proved
only for prime coefficients; arbitrary finite-ring coefficients need the explicit generic
construction and comparisons supplied here. An additive-map-to-linear-map shortcut in the
old ordinary-evaluation proof is valid for ZMod coefficients but cannot be reused for an
arbitrary ring; the new proof retains linearity throughout in ModuleCat.

No forced adaptation is needed. Preflight requires upstream source declarations to remain
verbatim, so the generic coefficient variant lives in a new Sheaf module and the original
source file is unchanged. No existing definition or statement is repaired.

## New nodes

`def-weil-pbc-finite-ring-torsor-associated-module` records the explicit generic
presheaf-and-sheafification construction in
`Sheaf.AlgebraicGeometry.FiniteRingTorsorAssociatedModule`, using the same formulas as
the existing prime specialization.

`lem-weil-pbc-finite-ring-torsor-module-comparisons` records the proved natural
pullback comparison and the rank-one trivial-representation comparison. Its graph-splitting
and local-bijectivity proofs have no remaining obligations.

`lem-weil-pbc-finite-ring-torsor-module-descent` records the proved recovery theorem:
construct the representation on sections over the torsor, build normalized equivariant
evaluation, prove its local bijectivity, and invert it by sheafification.

No change record is required: every existing definition and statement remains unchanged.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
