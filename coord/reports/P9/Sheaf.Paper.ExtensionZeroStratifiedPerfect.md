## What changed

Proved `AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect` by explicit
closed-complement vanishing and assembly of the finite open-closed stratification.
The closed stratum uses the zero perfect complex; the original strata retain their
covering sieves, complexes and perfectness certificates.

Added and proved `Sheaf.Paper.ExtensionZeroPerfectModelTransport`. Its private
helpers construct the constant-realization/global-section adjunction, prove its
compatibility with actual ringed direct image using `exchangeScalar_comm`, and
obtain constant-realization/pullback compatibility by uniqueness of left adjoints.
Other helpers construct exact derived scalar equivalences on slices and compare
them with `integralLocalDerived`. Full faithfulness reflects the given local model;
the published open unit and pullback compositor then transport it. Every helper is
proved, and every definition is a construction without `sorry`.

Updated both DAG proofs to match the implemented arguments. Existing public
signatures and public imports are unchanged. The new module's proof imports are
`CompleteCompactSupportProetale`, `StrictTowerExchangeMateNormalization`,
`LocalizedModuleExactForSystems`, and `import all ProEtaleOperations` (needed for
its private scalar-equivalence and adjunction constructions). The assigned module
also uses the existing ringed open-closed vanishing theorem.

Both delivery modules compile through the remote launcher against the published
build. The initial validation also compiled both modules; its assigned-module axiom
probe could not obtain a compile-server answer within 230 seconds and is retried
by the delivery checks.

Added `coord/changes/P9-extension-zero-proof-elaboration-options.md` for the two
file-level proof elaboration settings added to the assigned module. The source-only
consumer audit lists all 130 downstream modules; none needs adaptation. The
preflight treats these commands conservatively as an interface change, although
they do not alter the mathematical API or export options to importers.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect`
(node `lem-cbc-extension-zero-stratified-perfect`).

The retained split theorem
`AlgebraicGeometry.Scheme.cbc_extension_zero_perfect_model_transport`
(node `lem-cbc-extension-zero-perfect-model-transport`) is now proved as well.
There are zero remaining `sorry`s in either delivered module, zero holes added,
and no remaining split obligations. The change removes one original hole, net 1.
The proofs use existing named declarations that may themselves still have holes,
including `cbcOpenUnit_isIso` and `exchangeScalar_comm`.

## No longer needed

Removed direct proof imports from the assigned module:
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`, and
`WeilConjectures.CategoryTheory.SiteMorphismComposition`.
No existing public imports were removed. No transitive module is claimed to leave
the targets' import closure. The finite partition uses an explicit `Fin.cases`
index, so the source-library `openClosed` stratification module is not imported.

Removed obsolete direct tool-use entries from the top-level node:
`lem-weil-pbc-profinite-coefficient-inverse-image`,
`lem-weil-pbc-site-morphism-composition`,
`lem-weil-pbc-left-exact-site-inverse-image-tensor`, and
`lem-weil-proetale-weakly-etale-localization`.
The proved transport node now uses the published `cbcOpenUnit_isIso`,
`AdicCoefficientDatum.pullComp`, and `exchangeScalar_comm` interfaces. Thus it
does not directly use the previous raw site-composition, ringed-open-comparison,
weakly-etale-localization or profinite-coefficient arguments. Those interfaces
retain their own dependencies; no transitive pruning is asserted.
All added proof imports are used. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

`IsIntegralStratifiedPerfect` realizes each model on the ambient scheme and then
restricts it. Its transport therefore also needs compatibility of completed
constant realization with inverse image. This is now proved explicitly from the
global-section adjunction and the normalized scalar square. The slice categories
on the two sides have different actual inverse-image coefficient presentations;
they are compared by exact scalar equivalences, rather than identified directly.

`LocallyClosedStratification` also requires constructible strata. Noetherianity
supplies those fields for the explicitly constructed strata. No existing
statement or definition was changed. The earlier report's remaining coefficient
comparison and scratch-type-mismatch claims are resolved by the delivered proof.

## New nodes

`lem-cbc-extension-zero-perfect-model-transport`, in
`dag/nodes/sec-smooth-purity/lem-cbc-extension-zero-perfect-model-transport.json`,
is a proved transport theorem for a single local model across an open immersion.
It is a strict part of original proof step 3, with unchanged covering member and
complex; it asserts neither a stratification nor closed vanishing. Its blueprint
ancestor is `thm-cbc-finite-extension`, with the intervening nodes recorded.
Its source is Bhatt--Scholze 6.1.12(1), 6.6.11 and Stacks 03CB, 09BN.

Edge cases: the argument uses terminal objects and universal adjunctions and
therefore also applies to the empty scheme, empty open and empty stratum. For
zero K or P it uses the same equivalences. No boundedness, perfectness, finiteness
or quasi-compactness hypothesis is imposed on this individual transport theorem.
There are no changed existing definitions or statements and no consumer
adaptations. The elaboration-options change record is
`coord/changes/P9-extension-zero-proof-elaboration-options.md`.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
