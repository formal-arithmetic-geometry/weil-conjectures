## What changed

Filled both holes in `Sheaf.Paper.CompletedDirectImageLimits`, preserving all theorem
signatures and all existing data definitions. Private generic lemmas identify normalized
evaluation with the derived mate, establish transition compatibility, identify canonical
Rlim projections with evaluated constant/limit counits, and transport the full distinguished
Roos triangle, including its shifted boundary. The strict tower projection evaluates to the
specified finite projection, is natural, and gives the exact completion-unit identity.

Reused the normalized strict reduction comparison in
`Sheaf.Paper.StratumCompletionUnitRestriction`. Its ordinary comparison agrees with this
module's comparison by the proved quotient-unit equation and uniqueness. Replaced the
normalization predicate by the equivalent existing `StratumReductionFormula`, eliminating
an expensive kernel conversion and the duplicate private localization construction.
The change record is `coord/changes/U2-completed-direct-image-normalization.md`.
The DAG proof route and proof dependencies are updated. No new modules or nodes.
The stratum module is now a public import because the equivalent predicate names its
representative formula; all other new imports serve proofs only.
On resumption, checked the retained packet against current sources and refreshed the
consumer table: `CompletedExchangeUnit` also uses the chosen comparison, with no
signature or proof adaptation required.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlim_roos`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerProjection_properties`.

Zero `sorry` remain in the item, and zero are added elsewhere. No statements are split off.
The complete file compiles without warnings in 46.6 seconds through `lcompile.py`.
The exact appended delivery axiom probe also compiled in 54.5 seconds, reporting
`SHEAF-PROBED 38` with no forbidden axioms or direct holes.
The proof uses existing named declarations in `StratumCompletionUnitRestriction` and
`TowerDerivedEvaluationNormalization`, including declarations whose proofs remain assigned
to other workers. This is a proof from the library's stated dependencies, not a claim that
the entire transitive import closure is axiom-clean.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.RightFractionDenseSubcategory`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`.

The duplicate private resolving-representative descent and K-flat pullback helpers are
unnecessary here because the normalized strict comparison already states that result.
The associated direct dependencies `lem-trf-right-fraction-dense-subcategory`,
`lem-trf-site-functorial-flat-resolution`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-ringed-topos-kflat-pullback`, and
`lem-weil-pbc-independent-sheaf-tensor-colimits` are not direct requirements of this proof.
Some remain needed by the reused comparison and other consumers; no such module is withdrawn.

Removed the obsolete direct `tool_uses` entry
`lem-weil-ringed-tower-pushforward-limit-comparison`; the remaining approvals stay in order.

The planned abstract augmented-diagram projection mate, ringed constant-tower normalization,
and ringed tower limit comparison
are not used directly: explicit adjunction calculations establish the needed identities.
Exact products enter through `completedRlim_roos`; right-adjoint product preservation handles
the actual product comparison. No upstream declaration is removed or reverted to `sorry`.
No entire module is withdrawn, and the blueprint unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The old plan duplicated the strict reduction normalization now present in the stratum
module. Its general comparison/evaluation/augmentation declarations apply to arbitrary
scheme morphisms; their signatures do not require the stratum restriction predicate.
The quotient-unit normalization identifies their chosen comparison with this module's
specified comparison. The mathematical statement is unchanged.

The old normalization representation incurred a roughly 20-second kernel conversion.
The equivalent predicate repair and generic private adjunction calculations are needed to
keep the complete single-file check within 60 seconds. The server also intermittently
returned busy/no-answer responses; those were retried, without changing limits or tools.

Delivery attempts 6 and 7 were externally terminated with exit 143 and no script
diagnostic, after earlier capacity/busy responses. No delivery push has been confirmed.
The source, node, change record and this report remain ready in the sandbox.
The first three resumed deliveries received no answer from the busy compile server
after 645 seconds each; nothing was pushed, and delivery is being retried as instructed.
A standalone `lcompile.py` request also returned the same busy-server response after
645 seconds, with no Lean diagnostic.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
