## What changed

Filled both original proof bodies without changing any existing public signature,
definition body, attribute, or public import. The main proof constructs its coefficient,
finite quotient, completion, exact scalar pullback, and normalized module restriction
witnesses. The two ambient clauses use the separate coefficient-independent scalar
extension/slice comparison, with its pure tensor and universal counit normalization.

Added Sheaf.AlgebraicGeometry.ProEtaleScalarExtensionSliceComparison, containing the
literal restriction abbreviation, a proved exactness theorem and its instances, the
comparison structure, and one postponed theorem. No data is chosen from an arbitrary
existence theorem in a definition. All helpers in the original module are proved and
private. Updated the original node's proof route and added the new node. The file-local
backward elaboration settings are documented in
coord/changes/n4-continuous-slice-elaboration-options.md.

The exactness proof uses preservation and reflection of finite limits and the
left-adjoint property of continuous cocontinuous restriction. The coefficient proof
uses the actual graph mate and the pinned object inverse-image comparison. Ordinary
module restriction is the unique left adjoint of the same direct image, and its unit
is checked on sections. Scalar extension along an isomorphism uses the proved
SheafOfModules.exists_scalarExtensionRingIso API. Exact left-derived uniqueness and
Mathlib's mapDerivedCategory comparison give the counit equations.

## Proved and sorry left

Original holes closed:

- AlgebraicGeometry.Scheme.ContinuousSlice.modules_exact: proved from Mathlib's
  continuous module pushforward API, without a new hole.
- AlgebraicGeometry.Scheme.ContinuousSlice.continuous_coefficient_slice_normalization:
  all five clauses assembled with a complete Lean proof. The ambient clauses are
  reduced to the separate generic comparison below; this is a decomposition of that
  part of the argument, not a claim that its K-flat proof is complete.

One hole added, and the only sorry remaining in the delivered files:

- AlgebraicGeometry.Scheme.proEtaleScalarExtensionSliceComparison, node
  lem-per-proetale-scalar-slice-comparison. It is the independent scalar-extension
  and unbounded derived restriction comparison from Step 7. It says nothing about
  continuous coefficients, finite quotient towers, completion, etale or immersion
  pullback, or the canonical unit of the module inverse image. Its source and full
  proof in words are in its docstring and node.

Across the delivered files, two original holes are removed and one strictly separate
hole is added. Existing imported theorem holes are unchanged.
The original module contains zero sorry. The new restriction exactness theorem and
all its supporting helpers are proved.

## No longer needed

Removed proof-only imports from the item:

- Sheaf.CategoryTheory.LocalizationInverseImageCoherence: exactness is proved directly.
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients.
- Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections: use the existing finite constant
  inverse-image and canonical discrete-continuous comparison APIs instead.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction.
- Sheaf.Paper.RingedTopoiDerivedPullback.
- Sheaf.Paper.KFlatRingedToposPullback.
- Sheaf.AlgebraicGeometry.UnramifiedMorphism: the Mathlib etale-to-weakly-etale instance
  already supplies the needed site object.

The K-flat resolution, localized tensor restriction, ringed-topos K-flat pullback and
ringed-topoi derived pullback nodes are no longer direct proof dependencies of the
item. They remain dependencies of the new generic comparison, so this delivery does
not claim those modules are globally pruned. No module is withdrawn. Original
statement dependencies and maintainer-approved tool_uses entries are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed or changed. The previous proof plan's generic
localization exactness lemma is unnecessary for literal restriction. Its ordinary
module comparison must still be normalized against the selected module adjunction;
uniqueness of an unnormalized abstract isomorphism would not prove the unit field.

The generic localized ring mate graph evaluation is needed to identify the selected
coefficient and module maps. Its existing node is now a proof dependency; its generic
use is reported for independent review rather than modifying maintainer tool approvals.
The existing scalar ring-isomorphism, residue-limit and coefficient-localization nodes
supply the other API bridges absent from the previous direct dependency list.

## New nodes

lem-per-proetale-scalar-slice-comparison, in
Sheaf.AlgebraicGeometry.ProEtaleScalarExtensionSliceComparison, isolates the normalized
ordinary and unbounded derived scalar-extension/slice comparison from Step 7, with
its own Stacks sources and proof. The original statement and the unit's route stay
unchanged. The statement applies to arbitrary ring sheaves, hence is independent of
the coefficient arithmetic and is used for both integral and rational ambient clauses.
Its edge cases include identity and zero coefficient maps and the empty scheme;
the tensor universal property and K-flat computation apply without additional
hypotheses. Existing declaration interfaces are unchanged. Preflight treats the added file-local
backward elaboration options as commands requiring a record; they are documented in
coord/changes/n4-continuous-slice-elaboration-options.md. The downstream tool found
zero importing Lean modules and no forced adaptations.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
