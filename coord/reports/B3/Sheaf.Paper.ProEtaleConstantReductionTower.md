## What changed

Replaced the sole sorry in `Sheaf.Paper.ProEtaleConstantReductionTower`,
`AlgebraicGeometry.Scheme.OrderedExchange.projection_isIso`, by a categorical
reduction to the perfect projection formula for one fixed quotient.
The original declaration signature, instance attribute, and public imports stay unchanged.
No existing definition or target statement changes.

The new module `Sheaf.Paper.ConstantPerfectQuotientProjection` defines exact derived
evaluation, the existing pullback/evaluation and direct-image/evaluation comparisons,
the pasted normalized finite tensor/pullback comparison, and its precise counit mate.
These definitions introduce no unproved data and no freely chosen comparison isomorphisms.
The parent proof uses Mathlib's `mateEquiv_vcomp` and `mateEquiv_counit` to identify
evaluation of the original projection, followed by the canonical invertible
pushforward/evaluation comparison, with that finite mate. Exact evaluation commutes
with homology, and componentwise invertibility of a homology natural transformation
detects invertibility of the strict-tower map. This uses neither faithfulness of
derived evaluation nor equality detection by evaluation.

The finite module also contains fully proved private preparation for its source proof:
`scalarResolution` realizes a bounded finite-projective scalar resolution by an actual
augmentation quasi-isomorphism; `constantUnit` identifies the constant scalar module
with the sheaf tensor unit; `constantFiniteRetract` constructs its finite-free
retractions; and `constantResolution` realizes the bounded augmented resolution on the
original pro-etale site, including its strict-perfect package and flat K-flat property.
The final normalization of the finite mate with finite-total tensor projection remains
in the separate source lemma below. The original-site object and morphism universes
are preserved throughout. The downstream audit reports 86 transitive consumers and no
external explicit use of the instance name; no consumer signature or definition changes.
All original public declarations and docstrings below the proof are literally unchanged.

## Proved and sorry left

Validation: both sandbox Lean modules compile cleanly through `lcompile.py`; the
parent categorical proof checks in 6 seconds. The required delivery preflight checks
the packet again before pushing.

Closed the body of
`AlgebraicGeometry.Scheme.OrderedExchange.projection_isIso` (the item's only original
sorry), from the new finite source theorem and the existing canonical evaluation
comparison. The two private lemmas `isIso_of_evaluations` and `projection_evaluation`
are proved without new holes. The scalar and constant-resolution helpers listed above
are also proved without holes.

Added exactly one sorry:
`AlgebraicGeometry.Scheme.OrderedExchange.quotientProjection_isIso`, in
`Sheaf.Paper.ConstantPerfectQuotientProjection`, node
`lem-sp-constant-perfect-quotient-projection`. This is the Stacks 0944 perfect projection
formula for a single fixed perfect scalar quotient and its specified counit mate;
it contains no assertion detecting isomorphisms in a tower. Its docstring gives the
complete finite resolution and normalization argument. Its proof is exactly `by sorry`.

Thus the item has zero remaining sorries; the packet adds one elsewhere. This is a
one-to-one decomposition, not a net proof or a net reduction in the closure's hole count.
No sorry occurs in a definition, a private declaration, or a partially completed proof.

## No longer needed

No existing library module is withdrawn, and no global module pruning is claimed.
The parent's direct proof dependency `def-weil-pbc-projection-formula-arrows`
moves into the new finite source lemma's proof dependencies and remains needed there.
The node `lemma-weil-pbc-projection-formula-totalization` and its module
`Sheaf.Paper.ProjectionFormulaTotalization` are not needed on this route: the
finite proof uses the already proved, universe-independent chain theorem
`CategoryTheory.tensorAdjunctionTotal_isIso`, reexported by the retained arrow API,
rather than the equal-site-universe ringed-site totalization theorem. This does not
withdraw that module or assert that its other consumers no longer need it.
The parent now needs only the finite theorem, the canonical strict-tower evaluation
comparison, and homology conservativity for this part of its argument.

Removed redundant exploratory direct proof imports of
`Mathlib.Algebra.Homology.DerivedCategory.Fractions` and
`Sheaf.Paper.StrictPerfectPackageOnSite` from the new finite module; the APIs used by
the proved helpers are already exposed by the retained imports. Removed an unnecessary
public wrapper theorem for the already proved `ProEtale.StrictTower.evalR_isIso`.
There are no removals from the original item's imports.

## Where the brief, the DAG or earlier work was wrong

The existing totalization and projection APIs do not by themselves identify the exact
constant-coefficient finite mate on the original site: completed-coefficient formulas
use another coefficient ring, and the general ringed-site statements use a small-site
presentation with equal site universes. Applying either without the normalized scalar
and representative comparisons would leave a gap. The new finite statement records
that genuine source specialization explicitly; the parent now supplies all tower and
mate-pasting glue in Lean. No statement is disputed or weakened, and the blueprint
unit route is retained.

Checked the new statement against rank-zero terms, the zero and unit ideals, zero
quotients, empty sites, and an unbounded input: none requires an extra hypothesis.
The boundedness is only that of the perfect coefficient resolution, not of the input.

## New nodes

`def-sp-constant-quotient-projection` records the five canonical finite evaluation and
mate definitions in `Sheaf.Paper.ConstantPerfectQuotientProjection`. The construction
uses only the already normalized reduction and evaluation comparisons.

`lem-sp-constant-perfect-quotient-projection` records the separate single-quotient
perfect projection formula, with source, full proof in words, three Mathlib searches,
and the exact Lean attachment. The parent node `lem-sp-completion-mate-comparison`
changes only its proof, proof dependencies, and proof origin to match the categorical
reduction. No definition or statement repair, change record, or forced consumer
adaptation is needed.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
