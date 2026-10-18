## What changed

Filled all three proofs in `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`.
The existence proof uses the native chart construction `homOfIsFreeGenerator` on the
nonvanishing zero-locus cover, transports the ordinary pullback isomorphism through the
specified tensor-pullback adjunction, and proves uniqueness from standard-open coordinate
ratios. The two specification theorems then follow from `choose_spec` and pullback
extensionality. The direct imports were reduced to the modules used by this proof.

Two downstream consumers required forced public imports of
`WeilConjectures.AlgebraicGeometry.Ample` because they use `nonvanishingLocus` in their
signatures. Their original compiler errors were unknown-identifier errors for
`AlgebraicGeometry.Scheme.Modules.nonvanishingLocus` at lines 80, 82, 83, 86 of
`PointTangentSeparationClosedImmersion.lean`, and line 78 of
`SymmetricProductProperties.lean`. The added imports are the only changes in those
modules; both compile, and all fourteen downstream modules were checked with the overlay.

## Proved and sorry left

Proved (3 of 3 holes):

- `AlgebraicGeometry.ProjectiveSpace.generatingSections_integralHom_exists`
- `AlgebraicGeometry.ProjectiveSpace.integralHomOfGeneratingSections_spec`
- `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections_spec`

No `sorry` remains in the item, and no new `sorry` was added. The proof uses the existing
stated dependencies `generating_sections_iff_stalk_span` and `invertible_stalk_linearEquiv`.

## No longer needed

The old direct imports `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints` and
`Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre` are no longer needed by this
proof. The planned finite-index reindexing route and its supporting reindexing modules are
also unused: the native chart construction works directly for every finite coordinate type,
including the empty type. In particular, neither
`lem-weil-pbc-projective-space-finite-index-iso` nor
`lem-weil-pbc-projective-space-reindex-is-iso` is required on this route. The proof does not
need a new intermediate theorem or module.

The full list of Sheaf modules removed from this item's import closure (other targets may
still need them) is:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule`
- `Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`
- `Sheaf.Paper.NonvanishingSectionTrivializes`

## Where the brief, the DAG or earlier work was wrong

The earlier proof docstring described enumeration by `Fin (card I)` and a separate empty-index case.
The source-library `homOfIsFreeGenerator` construction already accepts an arbitrary finite
index type and supplies the required cover and twisting isomorphism, so that route was
unnecessary. The target statements and all definitions are unchanged. Removing the old
public re-exports exposed two missing direct imports in downstream signatures; those forced
adaptations are recorded in `coord/changes/ProjectiveSpaceHomGeneratingImports.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion` (unclaimed) originally failed with unknown
`AlgebraicGeometry.Scheme.Modules.nonvanishingLocus` at lines 80, 82, 83, and 86.
`Sheaf.AlgebraicGeometry.SymmetricProductProperties` (held by J8) originally failed with the same unknown identifier at line 78.
Adding `public import WeilConjectures.AlgebraicGeometry.Ample` to each module is necessary
because that module declares the name; the existing signatures and proofs are unchanged.
The changed lines are the added public import at line 11 of
`Sheaf.AlgebraicGeometry.SymmetricProductProperties` and line 11 of
`Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion`.
The original error was `Unknown identifier AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`;
the adapted modules compile against the changed dependencies.

## New nodes

None.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SymmetricProductProperties
Original against changed dependencies failed:
```
/tmp/forced-adaptation-26tgw64d/lean/Sheaf/AlgebraicGeometry/SymmetricProductProperties.lean:78:10: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`

Note: A public declaration `Scheme.Modules.nonvanishingLocus` exists but is imported privately; consider adding `public import WeilConjectures.AlgebraicGeometry.Ample`.

(with the modules compiled into /tmp/forced-adaptation-26tgw64d/.lbuild) [4.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
