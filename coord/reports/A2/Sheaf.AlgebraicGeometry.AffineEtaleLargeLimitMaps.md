## What changed

Replaced the sole sorry in
`AlgebraicGeometry.ProEtale.affineEtale_largeLimit_preservesColimit`
by a complete Lean proof from the existence and same-stage eventual-equality
parts of the stated finite-presentation argument. Reflection through
`Scheme.ProEt.forget X` gives the limit in the site. Taking opposites gives
the colimit cocone; `Types.FilteredColimit.isColimitOf'` proves its coyoneda
image is colimiting, and
`preservesColimit_of_preserves_colimit_cocone` gives the original conclusion.
The original theorem statement and public import are unchanged.

Added two modules, each containing one named geometric obligation:
`Sheaf.AlgebraicGeometry.AffineEtaleLargeLimitFactorization` and
`Sheaf.AlgebraicGeometry.AffineEtaleLargeLimitEquality`. These are the two
separate clauses (b) and (a) of the proof of Stacks Tag 01ZC, specialized to
the parent theorem's affine étale system and its larger index universe.
Neither asserts preservation of a colimit, and neither alone supplies the
parent theorem. Both retain all the parent's geometric and size hypotheses.
Their docstrings and nodes record the source and the finite-chart argument.

Validation: `lcompile.py --all` compiled all three modules, respectively in
3.3, 3.4 and 3.1 seconds, with no warnings or errors. The final item module
also compiled in 2.9 seconds after removal of the redundant direct Mathlib
import. The constant diagram, empty source stage, and empty-base cases were
checked against the two new statements: identity refinement handles equality
on an empty stage; factorization includes the empty-stage alternative and does
not require a nonempty scheme. Cofilteredness, and not an added preorder
assumption, supplies the refinements.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.ProEtale.affineEtale_largeLimit_preservesColimit`
(node `lem-pe-affine-etale-large-limit-maps`). No sorry remains in the item module.

Two holes added, both public theorems with proof exactly `by sorry`:

- `AlgebraicGeometry.ProEtale.affineEtale_largeLimit_factorization`,
  node `lem-pe-affine-etale-large-limit-factorization`.
- `AlgebraicGeometry.ProEtale.affineEtale_largeLimit_eventualEquality`,
  node `lem-pe-affine-etale-large-limit-equality`.

This is a decomposition of one hole into two strictly smaller steps, not a
complete geometric proof or a net reduction of the hole count. Net holes: +1.
There are no new definitions, axioms, or holes inside partial proofs.

## No longer needed

No existing module or node is globally pruned. No original import was removed.
The trial direct import of
`Mathlib.CategoryTheory.Limits.Types.Filtered` was redundant through the
existing public dependency and was removed after successful compilation.
The final proof adds only the two private proof imports for the new steps.

The parent no longer directly cites the small-index factorization and equality
nodes in its proof dependencies. Those nodes remain below the two new
geometric nodes as the finite-presentation proof templates; they are not
claimed to have become unnecessary to the overall route.

## Where the brief, the DAG or earlier work was wrong

The parent's proof steps describe applying the small-index Mathlib results at
a larger index. Reading their full declarations reveals a size mismatch:
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` and
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` fix `I : Type u`
when the schemes are `Scheme.{u}`. The assigned statement fixes
`I : Type (u + 1)`. The finite-presentation ring lemmas allow independent
index universes but require preservation of the underlying-set colimit;
the usual filtered-ring instance does not itself bridge that gap. No
universe equality, smallness assumption, or stronger limiting-cone hypothesis
has been added to bypass it. The new geometric holes retain that remaining
universe-sensitive work explicitly.

LeanSearch, LeanFinder, Loogle and source grep found the small-index templates
but no direct larger-index instance. The library theorem
`coefficientComparison_representable_preservesColimit` also has the desired
larger-index continuity behavior, but import-direction checking shows that its
module already reaches this item; using it would close an import cycle.
The current unit route remains unchanged.

## New nodes

`lem-pe-affine-etale-large-limit-factorization`, in
`dag/nodes/sec-proetale-coefficients/`, states only that a specified map from
the vertex to an affine étale target factors through a stage. Its declaration
is in `AffineEtaleLargeLimitFactorization.lean`; its source is the existence
clause (b) in Tag 01ZC. The node retains the local finite-presentation and
overlap-equality parts of that argument.

`lem-pe-affine-etale-large-limit-equality`, in the same directory, states only
that two maps from the same stage agreeing on the vertex agree after one
refinement. Its declaration is in `AffineEtaleLargeLimitEquality.lean`; its
source is clause (a) of Tag 01ZC. The node retains the diagonal-cover and
finite-generator equality argument. Both nodes inherit the item's chapter,
unit and blueprint ancestry. No existing interface changes or change records
are required.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
