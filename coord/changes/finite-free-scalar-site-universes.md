# SheafOfModules.finiteFreeScalarExtension

## Reason

The normalized coordinate construction works on a pro-etale site whose object and
morphism universes differ. The old private tensor helpers assumed SmallCategory.
Generalize those helpers to Category with a separate morphism universe and the
required sheafification instances, while retaining the existing public cochain theorem
verbatim. Reuse these helpers from FiniteScalarCoordinateData by a private all-import.
The finite-basis presheaf is itself a sheaf: transport the finite product sheaf structure
along its explicit coordinate isomorphism, making the sheafification unit invertible.
This replaces the heavier general restriction/sheafification comparison, preserving the
same pure-tensor coordinates. No definitions with postponed data or new holes are added.

## Old

```lean
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}
```

Private helpers use `changeOfRingsPresheaf.{u, u, u}` and `changeOfRings.{u, u, u}`.

## New

```lean
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}}
```

Private helpers use `changeOfRingsPresheaf.{v, u, u}` and `changeOfRings.{v, u, u}`.
The original SmallCategory context is restored before scalarComplexIso and the public
theorem. The public theorem signature and its normalization formula are unchanged.

Reviewer fix (2026-10-25): the general, basis-dependent extensionality lemma is named
`scalarExtension_hom_ext_of_basis` (arguments `φ d e M N f g h`, hypothesis through the
irreducible `tensorUnit`). The private `scalarExtension_hom_ext` keeps its original
signature and proof in the SmallCategory context, together with its original helpers
`restrictSheafifyHom`, `restrictSheafifyHom_toSheaf` and `restrictSheafifyIso`, because
`Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates` uses it through
`import all Sheaf.Paper.FiniteFreeScalarExtension` (`scalarPure_hom_ext`); with the
changed signature that module failed to compile.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteFreeScalarExtension | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.Paper.FiniteFreeQuotientCompletion | unclaimed | Public theorem unchanged; private helper adaptation only. |
| Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates | unclaimed | Uses the private `scalarExtension_hom_ext`, kept with its original signature; no adaptation. |
| Sheaf.Paper.FiniteScalarCoordinateData | J7 | Public theorem unchanged; private helper adaptation only. |
| Sheaf.SixFunctors.FiniteFreeComparisonTransitivity | unclaimed | Public theorem unchanged; private helper adaptation only. |

No target statement meaning changes. No consumer adaptation is required.

The return of head `19b183949de` was a landing-attachment failure, not a
mathematical objection. For this record, the stage-3 landing tool's reviewer-fix
filename is `finite-free-scalar-site-universes.change.md`; its destination remains
`coord/changes/finite-free-scalar-site-universes.md`. The filename without
`.change` is not accepted as a reviewer-fix attachment.

## Status

landed 20261025T003325-L-3229127 2026-10-25 (merge of deliver/J7/Sheaf.Paper.FiniteScalarCoordinateData)
