## What changed

Proved `AlgebraicGeometry.ProEtale.finiteProper_classical_truncation` in
`Sheaf.SixFunctors.FiniteProperClassicalTruncation`, without changing its signature.
This Lean module and its existing DAG proof route are changed, with an import-change
record documenting the public reexports removed.

The proof first obtains the proper étale torsion bound on finite-coefficient module sheaves,
then uses classical descent and the bounded-below direct-image comparison. A proved local
sheafification-unit isomorphism identifies underlying set sheaves in the intrinsic coefficient
realization, allowing the bound to pass to the exact coefficient model of the statement.
Finite-interval dévissage and the existing left-completeness theorem extend the bound to
classical complexes unbounded below. The canonical truncation triangle proves invertibility
of the actual morphism in the statement. The finite-interval induction is a proved private lemma; all five coefficient-comparison
subproofs (including the constructed underlying-sheaf isomorphism) are proved locally.
Local proofs avoid repeated imported-axiom traversal by the delivery probe. Their contexts
are cleared of unrelated hypotheses before the comparison calculations.

Proof imports now use `ProperTorsionDirectImageBound`, `ModuleCohomologyConventions`,
`ProEtaleClassicalSheavesModules`, `SfIntrinsicRealizationTransport`,
`UnboundedDirectImageBoundedBelow`, `ProEtaleProductsExact`, and the source-library torsion,
left-completeness, and total-derived-functor APIs. Proof imports remain private. Statement
imports use Mathlib's fibre and derived t-structure APIs directly. No source-library file,
public declaration signature, target, or existing definition is changed; no consumer
adaptation is needed. The public-import cleanup is recorded in
`coord/changes/S9-finite-proper-classical-truncation-imports.md`; the downstream scan
reports zero Lean importers. The original `open` command is retained.

Validation: the proof compiles without warnings through `lcompile.py`. Profiling the
original organization gave 1.7 s for the final theorem elaboration and 20.1 s for its
axiom traversal; the local subproofs avoid repeating that traversal for private helpers.
Its theorem signature is byte-for-byte identical to the original. There are zero `sorry`
tokens in the delivered Lean file. The proof uses the stated relative fibre bound after
arbitrary base change; it does not require a finite-type base field or invertible coefficients.
The zero ring, empty schemes, e = 0, and negative truncation degrees introduce no excluded
cases. Existing imported theorems may themselves still depend on `sorry`; this delivery
closes this module's hole from the available named declarations.

## Proved and sorry left

Closed (1 of 1 original holes):
`AlgebraicGeometry.ProEtale.finiteProper_classical_truncation`
(node `lem-sfb-finite-proper-classical-truncation`).

Holes added: 0. Split off: 0. Holes remaining in the delivered modules: 0.

## No longer needed

Removed direct imports:

- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.SixFunctors.UnboundedClassicalTruncation`
- `Sheaf.AlgebraicGeometry.ProperHeartContinuitySections`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`

The sectionwise localization route is unnecessary: the relative heart bound comes directly
from proper étale cohomological dimension, so no local-neighbourhood vanishing, localization
of unbounded sections, or conservative evaluation is used to prove this theorem. The final
argument uses exact products and the generic derived truncation tower instead. The former
public imports of `BaseChangeConventions`, `RightDerivedFunctorOfQuasiIsoResolutions`, and
`TruncationsAndHomotopyColimits` are replaced by the particular Mathlib APIs needed by the
statement. `ProEtaleFiniteModules` is no longer imported directly, although the realization
API still depends on it transitively.

Removed from this node's direct proof dependencies:

- `det-pe-sections-conservative`
- `det-pe-topos-functoriality-inverse-image`
- `det-pe-unbounded-classical-truncation`
- `det-proper-heart-continuity-sections`
- `lem-sfb-finite-proper-classical-neighborhood-vanishing`
- `lem-sfb-proetale-object-inverse-image-restriction`
- `lem-sfb-unbounded-sections-localization`
- `lem-weil-proetale-weakly-etale-localization`
- `sk-def-sfb-derived-categories`
- `sk-thm-pe-direct-image-comparison`

Withdrawn obsolete top-level `tool_uses` entries: `det-pe-sections-conservative`, `det-pe-topos-functoriality-inverse-image`, `det-pe-unbounded-classical-truncation`, `det-proper-heart-continuity-sections`, `lem-sfb-proetale-object-inverse-image-restriction`, `lem-sfb-unbounded-sections-localization`, `lem-weil-proetale-weakly-etale-localization`, `sk-def-sfb-derived-categories`, `sk-thm-pe-direct-image-comparison`.

These are removals from this proof's route, not requests to delete any shared module.
For example, exact products may use conservative sections in their own proof, and retained
statement dependencies still record the meanings of the derived categories and truncations.
No module is withdrawn, and no adopted source declaration is removed or replaced.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG's localization argument is a valid plan,
but it introduces comparisons that the relative étale dimension bound avoids. The revised
proof follows the unit's étale-bound and transfer argument directly. No blueprint unit
statement or realized unit step is bypassed. There are no new nodes or unproved intermediate results.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
