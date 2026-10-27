## What changed

Preserved the exact statement of
`WeilConjectures.PointSystemInsertion.pointSystemInsertionComposition` and all original
public imports. Moved its fixed constructions and the previously proved support
lemmas verbatim to `Sheaf.Paper.PointSystemInsertionData`, publicly re-exported by the
original module. This permits independent sheaf-level steps without circular imports.
Byte comparison verifies that every moved support declaration and the main theorem
signature are identical to the current repository source.

Proved finite coefficient composition by uniqueness of the constant-normalized map,
and completed composition by projection to each finite coefficient ring. Constructed
the derived insertion with `Localization.liftNatTrans`; proved its component
factorization and composition for all derived objects with `Localization.natTrans_ext`.
The composition proof uses the actual specified derived compositor and the chain
insertion equality, without a faithfulness claim for derived evaluations.

Server lcompile checked the data module and both new statement modules. It checked
the completed parent proof in 32.7 seconds. Removed profiling settings and the one
reported unused simp argument before delivery. Clean delivery compilation passed
all four modules. The recorded Maps signature uses the validator's structure header
format; its unchanged fields are documented in the data node and change record.

Separated the remaining sheaf argument into normalized module/tensor comparisons and
strict natural tower insertions. Their conclusions are strictly separate parts of the
original theorem. The final proof combines them, updates only the u and I fields, and
preserves all previous comparison laws definitionally.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PointSystemInsertion.pointSystemInsertionComposition`
(node `lem-trf-point-system-insertion-composition`). This is a decomposition into two
remaining sheaf lemmas, not a proof independent of sorry. The finite/completed
coefficient laws, the lift of tower composition to chain composition, and the derived
localization/composition argument are fully proved.
No hole remains in the item's module or the extracted data module.

Added exactly two holes, each the whole proof of its named public theorem:

- `WeilConjectures.PointSystemInsertion.pointSystemNormalizedComparisons`
  (`lem-trf-point-system-normalized-comparisons`): construct d,t,b,j with their section,
  restriction, tensor and transition laws, assuming the separately proved coefficient laws.
- `WeilConjectures.PointSystemInsertion.pointSystemStrictInsertions`
  (`lem-trf-point-system-strict-insertions`): construct strict u from the normalized section
  comparisons and prove its tower composition.

Thus holes closed: 1; holes added: 2; net: -1. The already completed coefficient
construction, G exactness and sections exactness remain proved, with identical data.

## No longer needed

The direct proof of coefficient composition does not use
`lem-trf-constant-coefficient-composition` / `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`:
it uses uniqueness of the published sectionwise constant coefficient map directly.

The reindexing compositors are fixed data. The comparison step uses those actual
coordinates and the adjunction-normalized coefficient module pullback comparison;
it does not require the separate generic object-inverse-image or site-generator
composition theorems, nor the generic tensor-compositor generator theorem:
`lem-sfb-proetale-object-inverse-image-restriction`,
`lem-trf-site-inverse-image-composition-generators`,
`lem-sf-proetale-tensor-composition-unit` are removed from the route. The separate
K-flat derived pullback-composition assertion
`lem-weil-pbc-proetale-derived-pullback-composition` is not used to localize strict
insertions: ordinary exact-functor localization suffices, while the original public
API and tensorCompositor definition are retained.

The extracted data module removes these unused original private imports:

- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`
- `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Mathlib.CategoryTheory.Localization.Predicate`

Generic scalar-extension and pullback APIs remain mathematical dependencies of the
comparison step; removing their unused private imports from the data module does
not withdraw their declarations or claim to close their holes.

The strict tower composition is proved from presheaf functoriality and the normalized
section action of t; it does not apply the one-level theorem
`pointSheafInsertionCalculus`, whose coefficient universe is restricted. Its reindexing
compositor definition remains part of the unchanged data, so the corresponding module
is retained.

No module is withdrawn. Public imports are retained for interface compatibility;
transitively re-exported dependencies are not claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The stated generic constant-ring
composition theorem fixes the coefficient universe to the scheme universe, whereas
this item permits independent field and coefficient universes. Uniqueness of the
recorded sectionwise coefficient map applies in the actual containing universe.
The declared generator-based route
is longer than the direct uniqueness argument for the already recorded sectionwise
coefficient comparisons. Existing helpers proved coefficient construction and
exactness already; those were retained. The ordinary derived natural-transformation
universal property supplies the whole final localization step.

## New nodes

`def-trf-point-system-insertion-data` owns the unchanged extracted fixed constructions,
record and seven predicates, including their already proved support theorems. It
introduces no new mathematical object or assumption.

`lem-trf-point-system-normalized-comparisons` is the sheaf-comparison and tensor part
of parent steps 1, 3 and 4, with the original transition rule. It assumes only the
coefficient laws proved in the parent and has no assertion about point insertions.

`lem-trf-point-system-strict-insertions` is parent steps 5 and 6 in restriction
coordinates. It gives strict natural insertions with their tower identity,
without any derived assertion or coefficient/tensor-comparison existence assertion.

Change record: `coord/changes/R1-point-system-insertion-data.md`. The only transitive
consumer is `Sheaf.TraceFormula.LocalNormalizationStrictRealization`; all types and
constructions remain identical through the public re-export, so no adaptation is needed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
