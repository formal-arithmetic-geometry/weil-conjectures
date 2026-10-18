## What changed

Proved `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_proper` in the assigned
module, with its exact signature and two public imports unchanged. The proof reuses the existing
`hasConstructibleDirectImages_of_isProper` from
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper`, handles the empty target explicitly,
and converts the constructibility and derived-category conventions with the proved
`Scheme.isConstructibleEtaleModuleSheaf_iff` and `rightDerivedFunctorPlusCompatibility`.
Only proof imports, the proof/docstring and the node's route fields change. No definition,
statement, consumer module or target changes. No new module or node is introduced.

The launcher single-file compile passed (12.9 seconds, no diagnostics). The import-direction
check permits the source Proper module. The source theorem uses only the target structure map,
so the existing statement's lack of an `f.IsOver` hypothesis is respected.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_proper`
(node `thm-fin-proper-constructibility-complete`). Added 0 holes; split off 0 statements.
The delivered module has 0 `sorry`s, and no `sorry` remains anywhere in this delivery.
This is a proof from existing declarations, not a decomposition. Existing downstream source
obligations, including projective-line constructibility and the projective reduction, are
unchanged; this report does not claim their transitive axioms are already closed.

## No longer needed

Removed these proof-only imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`
- `Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.NoetherianChowModification`
- `Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`
- `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The replacement proof imports are
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper` and
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
The statement still needs the existing public ConstructibleHigherDirectImages and Proper imports.

Pruned from this node's proof dependencies:

- `lem-weil-pbc-locally-noetherian-quasi-separated`: no separate qcqs locality argument.
- `lem-weil-pbc-proper-base-change`: no affine-target restriction.
- `def-weil-pbc-constructible-complexes`: no direct partition manipulation in this proof;
  its definitions remain statement dependencies through property C.
- `lem-weil-pbc-derived-open-restriction`: the source theorem works on the whole target.
- `lem-weil-pbc-constructible-qcqs-affine-local`: no affine-target gluing.
- `prop-weil-pbc-inverse-image-modules-exact`: no inverse-image construction in the adapter.
- `def-pc-projective-morphism`: source theorem uses an explicit closed projective embedding.
- `lem-weil-pbc-reduction-universal-homeomorphism`: source Chow modification allows nilpotents.
- `thm-weil-pbc-universal-homeomorphism-invariance`: no separate reduction descent.
- `lem-weil-pbc-module-sheaves-enough-injectives`: the proved derived compatibility is used
  directly instead of constructing a new injective resolution.

All seven former top-level `tool_uses` entries are obsolete for this route and removed:
derived-open-restriction, constructible-qcqs-affine-local, proper-base-change,
reduction-universal-homeomorphism, universal-homeomorphism-invariance,
inverse-image-modules-exact, and module-sheaves-enough-injectives (with their original prefixes).

The Noetherian induction, Chow modification, projective constructibility and modification
transfer nodes remain needed in the reused source proof; their separate Sheaf realization
modules are not needed as direct imports here. The finite-surjection cancellation node records
that source proof's empty-source branch. Pruning here describes this item's route; it does not
claim these modules are unreachable from every other target or from the replacement import's
transitive closure. The unit `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`,
so no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned six-step proof overlooks the existing implemented source theorem with the same
blueprint tag. Its global Noetherian Chow modification works without the affine-target and
reduced-source restrictions of the separate Sheaf realization, removing the separate locality
and reduction arguments. Updated the DAG to describe the actual source proof and the convention
adapter, and retained the mathematical dependencies used by that source proof. The theorem's
statement is unchanged. Empty targets, empty sources, degree zero and arbitrary nonnegative
degrees are all covered; no exponent is descended from an empty target.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
