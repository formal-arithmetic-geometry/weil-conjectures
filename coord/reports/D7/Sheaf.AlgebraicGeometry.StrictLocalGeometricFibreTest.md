## What changed

Replaced `AlgebraicGeometry.Etale.strictLocalGeometricFibreTest`'s hole by a complete Lean
proof of its unchanged statement. It removes the inverse-image composition transport,
uses exact conservative sections to pass to the homology sheaf of the derived unit,
and tests that sheaf map on every strict-local geometric fibre.

Added nine modules. Seven contain complete proofs: `AffineClosedSepClosedSectionsExact`,
`CohomologyPullbackExactConservative`, `StrictLocalBaseAffine`, `StrictLocalBaseIndEtale`,
`StrictLocalBaseGeometry`, `StrictLocalBaseSections`, and `StrictLocalFibreDerivedUnit`.
The affine exactness proof uses the existing acyclicity theorem to make the constant integer sheaf projective, then identifies its additive
coyoneda functor with global sections. The generic cohomology criterion uses the existing
Ext comparison and Leray isomorphism. Surjective global germs make sections faithful;
balancedness then proves conservativity. The fibre detection proof uses the existing
conservative family of universe-lifted geometric points.

The two remaining parts of the original argument are stated in `StrictLocalBaseGlobalGerms`
and `StrictLocalFibreUnitStalks`. Their docstrings contain the full mathematical arguments,
including the actual canonical-map compatibility and the point/lift projection equation.
The definition `derivedPullbackUnitHomology` is the explicit image of the existing derived
adjunction unit under the homology functor. No existing definition or signature changed.
The existing node's proof route and proof dependencies now match this reduction.

Validation: all ten delivered Lean modules compile together in import order, with no
warnings. The main theorem's last complete compile took 39.1 seconds.
The delivery dry run passed preflight. Its axiom probe for the main item timed out at
60 seconds; the tool explicitly records that the merge will run that probe again.
The remaining nine axiom probes reported no failure. This delivery does not claim
that the main item's axiom probe completed.

Edge cases checked mathematically: degree zero, positive degrees, the zero coefficient
sheaf, disconnected/profinite bases with multiple lifts, and separably closed imperfect
fields. No choice of one lift replaces the universal quantifier. The clopen argument
also covers an empty base, although the specified map u supplies a point in this setup.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.strictLocalGeometricFibreTest` (1 of 1).
This is a decomposition, not an axiom-free solution of the original mathematical problem:
it adds two strictly smaller obligations and has net hole count -1 before considering
any changes in the targets' import closure.

Complete new proofs:

- `AlgebraicGeometry.Scheme.affineClosedSepClosed_sections_preservesFiniteColimits`.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_iff_isIso_derivedPullbackUnitHomology`.
- `AlgebraicGeometry.Etale.strictLocalBase_isAffine`.
- `AlgebraicGeometry.Etale.strictLocalBase_indEtale`.
- `AlgebraicGeometry.Etale.strictLocalBase_geometry`.
- `AlgebraicGeometry.Etale.strictLocalBase_sections_exact_conservative`.
- `AlgebraicGeometry.Etale.strictLocalFibre_derivedUnit_iff`.

Every new hole, and no others in the delivered files:

- `AlgebraicGeometry.Etale.strictLocalBase_globalGerms`, node
  `lem-weil-pbc-strict-local-base-presentation`: still needs clopen representatives
  with extension by zero proving surjectivity of global germs. The categorical exactness and conservativity
  consequences, affineness, canonical coordinate-ring ind-etaleness, and the
  closed-point/separably-closed-residue-field calculation
  are already proved separately.
- `AlgebraicGeometry.Etale.strictLocalFibre_unit_stalks`, node
  `lem-weil-pbc-strict-local-fibre-unit-stalks`: still needs the identification of points
  with all lifts, strict localization with Spec K, and the canonical unit/restriction
  calculation using unrestricted strict-local stalk comparison. The passage from these
  pointwise statements to a sheaf isomorphism is already proved separately.

Thus the item module has zero holes and the complete delivery has two. Existing imported
obligations, including affine closed-point acyclicity, retain their own nodes and proofs
in words; they are not new holes introduced by this delivery.

## No longer needed

All original proof-only imports are removed from the item module:

- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`.
- `Mathlib.CategoryTheory.Sites.Point.Basic`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit`.
- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic`.
- `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`.
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift`.
- `Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`.
- `Sheaf.Paper.StrictHenselizationFunctoriality`.

The long-exact-sequence route (`lem-weil-pbc-derived-functor-long-exact`) is unnecessary:
projectivity of the constant integer sheaf proves exactness directly from H¹ vanishing.
Neither long-exact-sequence wrapper is imported by the new proof modules. The extra
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives` and
`Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows` wrappers are unnecessary;
the existing derived-global-sections/Ext API already supplies the required structures
and canonical comparison. These removals are pruning of this route, not a claim that
other targets cease to use those modules.

The two unfinished modules retain only imports needed by their signatures; their proof
ingredients are recorded as node dependencies. The remaining removed imports express
geometry or stalk ingredients still needed by the
two lower obligations, or definitions already supplied by retained public imports.
In particular finite products of fields, profinite topology, affine acyclicity,
unrestricted strict-local stalk comparison, inverse-image germs, and geometric stalk
conservativity are retained in the lower modules or their node proof dependencies.
The two missing clopen attachments described below are also pruned from the dependency
route; their needed arguments are contained in the new obligations.
No blueprint unit or realized unit step is bypassed. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node records for `lem-weil-pbc-clopen-etale-neighbourhood-cofinality` and
`lem-weil-pbc-clopen-stalk-global-sections-detection` name Lean modules whose files are
absent in the supplied checkout:
`Sheaf.AlgebraicGeometry.ClopenEtaleNeighbourhoodCofinality` and
`Sheaf.EtaleCohomology.ClopenStalkGlobalSectionsDetection`.
Thus their recorded declarations cannot currently be imported. The new nodes include
the needed clopen arguments directly: only existence of pointed refinements and extension
by zero is required for global-germ surjectivity; the pointwise obligation additionally
includes equalization and the strict-localization colimit calculation. The two missing
attachments are no longer dependencies of this route.

Affineness in step 1 follows directly from the existing closed-point structure theorem
and Mathlib pullbacks, without constructing the finite-product presentation.

Canonical ind-etaleness is also proved from the existing affine-chart theorem by the
Mathlib ring-pushout and base-change APIs.

The ring-theory API also shortens step 2: ind-etale implies weakly etale, and the flat
multiplication criterion gives absolute flatness. Its prime ideals are maximal. Existing
residue-field separability then identifies every residue field with K.

The existing Ext-to-derived-global comparison gives a shorter implementation of step 5
than proving separate degree-zero and positive-degree Leray arguments. The projective
Ext¹ criterion similarly avoids the planned long exact sequence in step 4.

## New nodes

`lem-weil-pbc-affine-closed-sepclosed-sections-exact`: proved categorical exactness from
existing affine closed-point acyclicity, with the adjunction/coyoneda identification.

`lem-weil-pbc-cohomology-pullback-exact-conservative`: proved generic derived-unit
criterion, and records its concrete homology-map definition.

`lem-weil-pbc-strict-local-base-affine`: proved affineness by factoring both legs through
an affine chart containing the image of the strict-local closed point. This works over
any field K.

`lem-weil-pbc-strict-local-base-ind-etale`: proved canonical coordinate-ring ind-etaleness
by the existing affine-chart theorem, ring pushouts and base change. This works over any
field K.

`lem-weil-pbc-strict-local-base-presentation`: the global-germ part of steps 1--3, one remaining
global-germ-generation obligation. Affineness and ind-etaleness are proved separately.

`lem-weil-pbc-strict-local-base-geometry`: proved closed points by absolute flatness, and
separably closed residue fields by separability over K, transported through the affine
spectrum and residue-field isomorphisms.

`lem-weil-pbc-strict-local-base-sections`: proved step 4 from geometry, affine exactness,
and the faithful geometric stalk family.

`lem-weil-pbc-strict-local-fibre-unit-stalks`: original step 6 and the point/lift
correspondence, one remaining pointwise canonical-map obligation.

`lem-weil-pbc-strict-local-fibre-derived-unit`: proved step 7 by geometric stalk
conservativity from the pointwise comparison. No change records are needed because no
existing statement, definition, or public import changed.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
