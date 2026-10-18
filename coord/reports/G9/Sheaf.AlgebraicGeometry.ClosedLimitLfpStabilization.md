## What changed

Proved `AlgebraicGeometry.exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation`
in `Sheaf.AlgebraicGeometry.ClosedLimitLfpStabilization`, preserving its complete signature.
Two proved private helpers first handle qcqs diagrams with monomorphic affine transitions,
then apply that result to affine open restrictions of the original system. Mathlib's
morphism factorization descends the identity of the limit; eventual equality descends the
inverse equation. Monomorphism cancellation gives two-sided inverses at all later stages.
A finite affine cover and locality of isomorphisms give the original conclusion without
assuming quasi-separatedness of the original stages or base.

Added a proof-only import of `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
Removed an unused public import and three unused proof imports as detailed below.
Updated the item's DAG proof and dependencies to the actual route, retaining the unit's
proper base change route. Added one Mathlib leaf documenting the exact eventual-equality
input; it adds no Lean declaration or hole. The declaration's original docstring is retained;
its polynomial-kernel plan is superseded by the DAG proof and the implementation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation`
(node `lem-weil-pbc-closed-limit-lfp-stabilization`).
Added 0 holes; split off 0 obligations. No `sorry` remains in the delivered Lean module.
Both private helpers are fully proved. The final proof uses only Mathlib declarations.
The pruned item compiled cleanly in 4.4 seconds; its unchanged direct consumer
`Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization` compiled against
that sandbox output in 2.3 seconds. Mechanical signature comparison reports no changes.
Every line of the delivered Lean file has at most 100 characters.

Edge cases: a finite affine cover may be empty; `Finset.exists_le` takes an upper bound
of the empty image because the ambient index type is nonempty. The locality theorem
also handles the empty cover. Neither a least stage nor antisymmetry of the preorder
is used. No global quasi-separatedness instance is introduced.

## No longer needed

Removed `public import Sheaf.AlgebraicGeometry.LimitAffineTransition`.
The proof starts from the given limiting cone and uses Mathlib `isLimitOpensCone`, so it
needs neither construction of a new limit nor affine colimit comparison. The corresponding
node `lem-weil-pbc-limit-affine-transition` remains a statement dependency of the original
DAG statement but is no longer a proof dependency or a Lean import of this item.

Removed proof imports `Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`Mathlib.RingTheory.FinitePresentation`.
Removed proof dependencies `lem-pc-filtered-colimit-commrings-elementwise`,
`lem-weil-pbc-lfp-affine-opens-finite-presentation`, and
`lem-weil-pbc-finite-presentation-surjection-kernel-fg`: morphism descent replaces the
explicit representative, finite polynomial-kernel, and eventual vanishing arguments.
Retained `lem-weil-pbc-scheme-morphism-gluing`, used through Mathlib's locality of
isomorphisms, and the finite type/closed immersion definitions. No unit realization
module is bypassed: this item is auxiliary, not a realized unit statement or step.
Whether removed dependency modules remain reachable through other parents is left to
the maintainer's closure computation.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement. The original proof plan missed a shorter route
through the already proved Mathlib morphism descent theorem and eventual equality theorem.
The global descent theorem requires qcqs stages: applying it directly to this item would
be invalid. Applying it only after affine restriction preserves the stated hypotheses.
The source was read at Stacks Limits, Tag 081B(3), and the Mathlib theorem signatures and
section hypotheses were read in `AffineTransitionLimit.lean`.

Searches: LeanFinder for closed inverse-system stabilization returned Mathlib morphism
equality lemmas but no exact stabilization theorem; Loogle and source grep located the
finite-presentation factorization theorem. DAG and blueprint searches found the existing
factorization and restricted-limit leaves and no eventual-equality attachment. LeanSearch,
Loogle and source grep each found the exact eventual-equality theorem recorded below.

## New nodes

`lem-weil-pbc-locally-finite-type-limit-map-equality` is a Mathlib leaf, attached to
`AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`.
It states eventual equality of two maps from one stage to a locally finite type target,
with quasi-compact stages and affine transitions, exactly as Mathlib states it. No new
Lean module, unproved theorem, or mathematical dependency outside Mathlib is added.

Change record: `coord/changes/G9-closed-limit-lfp-stabilization-import-pruning.md`.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
