## What changed

Filled `WeilConjectures.CompletedStalk.sectionRestriction_existsUnique` in
`Sheaf.Paper.CompletedStalkReparametrizationCoherence`. The proof constructs the
natural transformation from section restriction, checks its linearity using the
proved constant-scalar normalization in `PointAutomorphismRestrictionNatural`, and
proves it is invertible because restriction is along an isomorphism of site objects.
The prescribed action on every section proves uniqueness. Added a proof-only
`import all Sheaf.Paper.PointAutomorphismRestrictionNatural` to access the proved
normalization helper; no existing statement or public import changed.
Disabled the extra
`pointRestrictionScalarDerived` instance introduced by the private proof import,
so the file keeps using its original derived-category presentations.

The private `restriction_scalar` theorem proves the scalar identity.
`restrictionTransformation` stores the real linear restriction maps and their
naturality; its irreducible wrapper and the proved
`restrictionTransformation_apply` API prevent repeated unfolding of completed
coefficient actions. The construction, invertibility, object transport and existence/uniqueness proofs
are generic in the scheme automorphism, before specializing to `sourceIso`.
The `restrictionTransformation_heq` lemma explicitly transports between the
postcomposed final object and the statement's `sourceArrow`.
No helper contains a hole. The limit construction is kept
locally irreducible during this proof; no existing definition body is edited.

Factored the body of `derivedSectionRestriction` through a local function of
abstract abelian categories, exact functors and their sections isomorphism. Specialization
beta-reduces to the previous construction; this avoids repeatedly checking the
concrete `Spec` automorphism against large derived-functor expressions. The
signature and mathematical definition are preserved, with no consumer adaptation.
The detailed trace checks the refactored derived construction in under one
second; all diagnostic commands and options are removed from the delivered file.
The change record is
`coord/changes/S2-derived-section-restriction-generic-construction.md`.

Updated the item's DAG proof and dependencies for this argument. The general
restriction calculation is used as a tool from
`lem-weil-point-automorphism-restriction-natural`; it replaces no step of the trace
unit. The maintainer may record that tool approval when reviewing this packet.

## Proved and sorry left

Closed 1 of the item's 6 holes:
`WeilConjectures.CompletedStalk.sectionRestriction_existsUnique`.
Added 0 holes and split off 0 statements.

The following five holes remain unchanged, all attached to
`lem-trf-completed-stalk-reparametrization-coherence`:

- `WeilConjectures.CompletedStalk.towerReparam_existsUnique`
- `WeilConjectures.CompletedStalk.reparam_existsUnique`
- `WeilConjectures.CompletedStalk.rationalComparison_existsUnique`
- `WeilConjectures.CompletedStalk.rationalReparam_existsUnique`
- `WeilConjectures.CompletedStalk.coherence`

The previously proved `pointUnits` and `sectionsRoos_existsUnique` are preserved.
This is a partial proof delivery as allowed for a module containing several holes.
The delivery checks the complete module, including the definitionally equal derived construction and
unchanged rational constructions.

## No longer needed

Removed these redundant direct proof imports (their public declarations are
already available through retained public imports):

- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.Paper.PointProEtaleSectionsExact`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`
- `Sheaf.Paper.FiniteCoefficientPoint`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfRationalizationKaroubi`

Also removed the unused direct proof import
`Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`; the
current code uses no declaration from that module. This does not replace or
withdraw the normalization obligation in the unfinished coherence proof.
No DAG node or library module is withdrawn, and the remaining proof plan is
preserved. These import removals do not prune any globally reachable module.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The available public restriction theorem assumes
`l ≠ D.p`, whereas the item's section-restriction assertion has no such assumption.
Its proved scalar-normalization helper is independent of that assumption, so the
proof uses that calculation directly and proves invertibility and uniqueness here.
No characteristic hypothesis has been added. The identity automorphism and zero
module are included: restriction is still an isomorphism and the same
extensionality proof applies.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
