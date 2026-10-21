## What changed

Proved the complete original `WeilConjectures.point_sections_derived_reduction`
conjunction, with the same signature and the same point-section, coefficient, quotient
and tensor definitions. The repaired proof follows the original twelve steps:

1. The actual completed coefficient projection has a short exact uniformizer sequence.
   The new coefficient regularity proof uses finite quotient injections and inverse-limit
   projections, rather than an unproved normalization statement.
2. On flat-term K-flat sheaf models, exact sections give injectivity of the uniformizer
   power and the canonical quotient-section isomorphism from the existing resolution
   independence module.
3. Principal quotient preserves quasi-isomorphisms between complexes on which that
   scalar acts injectively. The proof uses the homology long exact sequence of the two
   degreewise short exact coefficient sequences, valid for unbounded complexes.
4. An ordinary flat-term K-flat resolution and counit naturality make the comparison
   invertible on the section complex. Resolution independence and a common resolved
   source for a derived roof prove naturality for all derived maps.
5. Universal uniqueness identifies the generic cochain derived extension with the
   project's prescribed homotopy presentation. Whiskering gives the required natural
   isomorphism on the integral constructible category.
6. The separate generic principal-quotient cone theorem proves the second clause using
   the two-term free quotient resolution, with independent localization Hom universes.
   Exact finite sections give the final homology comparison.

The existing shared definitions are factored into `PointSectionsDerivedReductionData`
and publicly reexported from the original item, without changing their bodies or
signatures. The abstract `PrincipalReduction.Setup` in the unclaimed
`DerivedReductionResolutionIndependence` module now accepts a specified surjective
presentation of the principal quotient, with its principal kernel and compatible scalar
map. This permits the target's actual `ULift (O_E/(pi^(n+1)))` rather than the only
isomorphic quotient of `ULift O_E`. The complete existing coherence proof is retained
and adapted to these equivalent presentation fields. No target definition changes.

All fourteen Lean files compile together through `lcompile.py --all`. Every new lemma
is proved in this packet. No source-library file is edited, and no adaptation of another
group's module remains.

## Proved and sorry left

Original item: **one hole closed, zero holes added, zero holes left**.
The closed declaration is `WeilConjectures.point_sections_derived_reduction`.
This is a proof, not a decomposition into retained holes.

The returned `WeilConjectures.point_sections_derived_reduction_iso` is now proved from
the original route. The returned cone obligation is replaced by the proved stronger
arbitrary-complex theorem
`WeilConjectures.point_sections_derived_reduction_module_cone`; the parent transports
it to any model of the integral section object. The homology component is proved as
`WeilConjectures.point_sections_derived_reduction_homology`.

The following new supporting theorems are also fully proved, with no `sorry`:

- `CochainComplex.PrincipalQuotient.quasiIso_map`
- `SheafOfModules.PrincipalReduction.Setup.alpha_isIso`
- `SheafOfModules.PrincipalReduction.Setup.comparison`
- `DerivedCategory.principalDerivedTensorCone`
- `AlgebraicGeometry.ProEtale.completedIntegralScalar_regular`
- `WeilConjectures.pointReductionQuotient_properties`
- `WeilConjectures.pointPrincipalReductionCoefficients`
- `WeilConjectures.scalarReductionCochainModel_iso`

There is no `sorry` in any delivered Lean file. The adapted existing
`SheafOfModules.PrincipalReduction.Setup.resolution_independence` remains completely
proved. Existing dependency statements are used through their declared interfaces;
this delivery does not claim to close unrelated dependencies.

## No longer needed

The proof has no dependency on `lem-trf-point-reduction-unit-normalization` or its
`PointReductionUnitNormalization` module. The earlier proposed import adaptations of
`PointReductionUnits` and `PointReductionUnitNormalization` are removed from the packet;
their existing repository files are preserved. No source declaration is withdrawn.

The old `point_sections_derived_reduction_components` placeholder is removed entirely:
it merely repackaged the isomorphism clause. The unused elementary
`point_sections_derived_reduction_t_injective` helper from the initial repair draft is
also removed. The retained isomorphism and cone wrappers have complete proofs from
strictly smaller generic results.

The coefficient-sequence proof does not use `CompletedConstantSheafReduction`: it
proves the required sequence directly using the finite-level divisibility theorem and
the completed scalar regularity theorem. The cone theorem uses its own principal
quotient calculation with the actual localization universes. Simultaneous diagram
replacement is not needed for the final naturality descent: a resolved source for each
roof suffices. The existing resolution-independence theorem, including its own proof
dependencies, is retained unchanged except for its quotient presentation interface.

Removed proof-only imports from the factored data module (each is either used explicitly
by the actual proof modules or unnecessary for this item's route):

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`
- `WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived`
- `Sheaf.Paper.DerivedReductionResolutionIndependence`

The parent imports only its data and three proved component modules. No module file is
withdrawn in this packet; removing a redundant direct import does not claim deletion of
an indirectly used dependency. The original twelve-step DAG text is retained, with
its dependencies pointing to the proved implementations of those steps.

## Where the brief, the DAG or earlier work was wrong

C6 is repaired: the isomorphism proof and DAG do not cite point-reduction unit
normalization. The item-to-normalization-to-item cycle is removed.

C7 is repaired: the proof follows the item's coefficient sequence, flat-term model,
ordinary quotient quasi-isomorphism, naturality, localization, cone and homology route.
It does not substitute a sorry in the other `sk-d-weil` unit for this argument.

D1 is repaired: no clause is moved to another sorry. Quotient quasi-isomorphism
preservation, completed coefficient regularity, the short exact coefficient sequence,
flat-model invertibility and roof descent are separate proved mathematical results.
Both the functor isomorphism and cone clause are now complete.

Two interface issues mattered in the actual proof. First, the abstract setup's canonical
quotient of a lifted ring is not definitionally the target's lifted quotient; the
specified-presentation generalization records the same mathematical principal quotient
and the actual scalar square. `tools/downstream.py --uses Setup` and
`--uses quotientSectionsMap` find no external users. Both existing DAG citers continue
to hold, as recorded in `statement_change`. Second, the source `reductionIso` has a
single localization-universe parameter. The generic cone proof builds its two-term
coefficient comparison in the actual arbitrary source Hom universe instead of requiring
that narrower presentation. No target statement is weakened in either case.

The finite constant-sheaf scalar identity was abstracted over the site before
specialization; this avoids repeatedly unfolding the large small-site sheafification
model. The final files compile under the ordinary per-file limits.

## New nodes

`lem-pod-principal-quotient-quasi-iso`: tensoring with a principal quotient preserves
quasi-isomorphisms on unbounded complexes with regular terms; proved.

`lem-pod-principal-reduction-flat-comparison`: invertibility on flat-term K-flat sheaf
models, using exact quotient sections and an ordinary flat resolution; proved.

`lem-pod-principal-reduction-comparison`: descent and naturality on the entire derived
category through resolved roofs; proved.

`lem-pod-principal-derived-tensor-cone`: the scalar-restricted chosen derived quotient
tensor is a multiplication cone in arbitrary localization Hom universes; proved.

`lem-pod-completed-integral-scalar-regular`: finite quotient injections detect
regularity on completed sections at every site object, including empty objects and
exponent zero; proved.

`lem-pod-point-reduction-coefficient-ring`: surjectivity, principal kernel and regularity
for the actual lifted quotient coefficient map; proved.

`lem-pod-point-principal-reduction-coefficients`: short exactness of the actual
completed coefficient sequence; proved for any field, without algebraic closedness.

`lem-pod-scalar-reduction-cochain-comparison`: universal identification of the cochain
and prescribed homotopy derived scalar-extension presentations; proved.

The retained earlier support nodes
`lem-pod-point-sections-derived-reduction-data`,
`lem-pod-point-sections-derived-reduction-iso`,
`lem-pod-point-sections-derived-reduction-cone`, and
`lem-pod-point-sections-derived-reduction-homology` are updated to the actual proved
implementation. They introduce no holes.

Change records:
`coord/changes/A6-point-sections-derived-reduction-data.md` and
`coord/changes/A6-principal-reduction-quotient-presentation.md`.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
