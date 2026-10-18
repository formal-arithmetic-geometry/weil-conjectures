## What changed

Proved `AlgebraicGeometry.exists_field_curve_completion_insep` with its existing signature
unchanged. The proof follows Tag 0GK5: dense projective completion, finite purely inseparable
geometric normalization, projective normalized components, finite separable constant fields,
and restriction back to the original dense open.

Added five completely proved helper modules: `FieldCurveCompletionCore`,
`ProjectiveGeonormalComponents`, `GeonormalProjectiveCurveConstants`,
`IntegralNormalizationOpen`, and `NormalizationDenseOpenComponents`, all under
`Sheaf.AlgebraicGeometry`. The component helper applies the existing component theorem after
reindexing by `ULift (Fin n)`, then transfers geometric normality using open coprojections
and stalk isomorphisms. The constant-field helper uses the existing global-sections and Stein
factorization theorems, converts separating-basis separability to algebraic separability for
a finite extension, and applies the proved smooth/geometrically-connected irreducibility
criterion. The open-normalization comparison is proved from the existing finite-normal
comparison theorem over a common dense isomorphism open. The component restriction helper
constructs actual pullbacks and proves their supports enumerate the open's components.

Existing public imports and theorem visibility stay unchanged. New modules expose only the
imports required by their statements; their proof inputs are ordinary imports. Updated the
parent DAG proof, dependencies, proof origin and obsolete tool approvals; added matching node
records with verbatim signatures and Mathlib searches for every new public helper. No existing
definition or statement was changed and no consumer adaptation is required.

## Proved and sorry left

Original holes closed: one, `AlgebraicGeometry.exists_field_curve_completion_insep`
(node `lem-weil-pbc-field-curve-completion-insep`).

Holes added: zero. Holes remaining in the delivered Lean files: zero. The five new public
helper theorems are all proved:

- `AlgebraicGeometry.exists_projective_geonormal_core`;
- `AlgebraicGeometry.projective_geonormal_components`;
- `AlgebraicGeometry.exists_geonormal_projective_curve_constants`;
- `AlgebraicGeometry.exists_integral_normalization_open`;
- `AlgebraicGeometry.exists_normalization_dense_open_components`.

The proof uses the project's existing named declarations as intended by stage 3, including
projective completion, geometric normalization, projective components, low-dimensional
smoothness, global-sections separability, Stein factorization and finite separable refinement.
There are no new holed declarations or postponed glue arguments. All six delivered modules
compile without warnings.

## No longer needed

Removed the following direct imports from the item:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`: the finite-etale section route is unnecessary.
- `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`: the already-proved
  `WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange` API is used directly.
- `Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety`: the already-proved
  `WeilConjectures.AlgebraicGeometry.GlobalSectionsProper` API is used in the constants helper.
- `Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`: smoothness plus Stein
  geometric connectedness implies geometric irreducibility directly.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`: actual integral component
  pullbacks and the finite-normal comparison prove precisely the open restriction needed here.
- `Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion` and
  `Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep`: still needed through the core helper.
- `Sheaf.AlgebraicGeometry.NormalizationProjectiveComponents`: still needed through the
  component helper; the previous universe issue does not justify pruning this dependency.
- `Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth`,
  `Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable`,
  `Sheaf.AlgebraicGeometry.SteinFactorizationAffine`,
  `Sheaf.AlgebraicGeometry.FiniteSeparableBaseRefinement`, and
  `WeilConjectures.AlgebraicGeometry.GlobalSectionsProper`: still needed in the constants helper.

The proof no longer needs the nodes `lem-weil-pbc-etale-section-clopen-immersion`,
`lem-exc-etale-coproduct-etale`, `lem-weil-pbc-etale-scheme-base-change`, or
`lem-weil-pbc-reduced-algebraic-normalization-field-change`. The corresponding separate
finite-etale/clopen argument and general field-change normalization theorem are pruned from
this route. The proof also replaces `lem-weil-pbc-finite-type-over-noetherian`,
`pqf-lem-lft-fp-locnoeth`, and `lem-weil-pbc-noetherian-open-subscheme-noetherian` as proof
inputs by direct Mathlib Noetherian and finite-presentation instances. Removed these seven
obsolete entries from the parent's top-level `tool_uses`, preserving the order of all retained
approvals. Reduction and coproduct notions remain statement dependencies; their definitions
are not withdrawn. Other dependencies moved into helpers remain needed, as specified above.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at the index-universe mismatch and left both the original hole
and a new core hole. The mismatch is real but is resolved by a finite `ULift` reindexing; the
projective component theorem is usable without changing its signature. Both previous holes
are now filled, and the remaining assembly is complete.

The old plan's separate proof of geometric normality after constant-field refinement is
unnecessary: the existing proved theorem
`GeometricallyIrreducible.of_smooth_of_geometricallyConnected` applies directly after smooth
base refinement and Stein factorization. The old general reduced-normalization field-change
statement is stronger than the open restriction needed here; the finite-normal comparison
supplies that restriction without any new unproved theorem. No mathematical statement was
weakened, no target changed, and the proper-base-change unit route is preserved.

Edge cases checked in the construction: an empty component family yields empty completion
and original scheme; dimension zero uses the same smooth constant-field argument; nonreduced
schemes are handled using integral closed component subschemes throughout, without changing
the original scheme or the normalization map's componentwise interpretation.

## New nodes

`lem-weil-pbc-field-curve-completion-core` matches
`AlgebraicGeometry.exists_projective_geonormal_core` in module
`Sheaf.AlgebraicGeometry.FieldCurveCompletionCore`, packaging the existing completion and geometric-normalization results.
The previous sandbox's placeholder Lean signature, empty searches and unproved theorem have
been replaced by a full signature, searches and a complete proof.

`lem-weil-pbc-projective-geonormal-components` matches
`AlgebraicGeometry.projective_geonormal_components`, including the finite-index universe
bridge and geometric-normality transfer to components. Its proof is complete.

`lem-weil-pbc-geonormal-projective-curve-constants` matches
`AlgebraicGeometry.exists_geonormal_projective_curve_constants`. It proves the finite
separable constant-field factorization, smooth projectivity and geometric irreducibility.

`lem-weil-pbc-integral-normalization-open` matches
`AlgebraicGeometry.exists_integral_normalization_open`. It proves normalization restriction
for an integral open immersion by finite-normal comparison; no hole remains.

`lem-weil-pbc-normalization-dense-open-components` matches
`AlgebraicGeometry.exists_normalization_dense_open_components`. It constructs and enumerates
the component pullbacks and compares their normalizations with the projective components.
No change record is required because no existing signature or definition changes.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
