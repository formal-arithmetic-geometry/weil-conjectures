## What changed

Completed `WeilConjectures.field_cohomology_perfect_descent_qbar` in
`Sheaf.Paper.FieldCohomologyPerfectDescent`, preserving all public signatures and definitions.
The original rational theorem and its proof remain unchanged. Added the private proof import
`Sheaf.Algebra.Homology.PerfectDualScalarCalculus` and the Hom-cochain single-object
equivalence import, and proved private helpers for the field
perfectness criterion, ordered model bounds, signed dual support and scalar comparison,
and a common support interval for a finite family of point objects.

The proof keeps `F = K.stage` and `K_F = K.obj`. The rational point fibres already lie in
`pointFiniteDimensional`; transport along the Shrink algebra equivalence followed by the
existing `DerivedCategory.isPerfect_iff` supplies bounded finite projective field models.
The normalized object formula of `pointQbarFibre` and the canonical stage functor give the
ordinary and compact presentation isomorphisms. The beta isomorphism of the signed dual
scalar calculus, projective Hom evaluation, and exact scalar extension identify both duals.
Finally, a finite-family support argument gives a single ordered interval for all four
cohomology objects. The empty support and zero-model cases are included by using ordered
bounds and an induction starting at [0,0].

Updated the item's DAG proof, proof dependencies and origin to describe this argument.
No new nodes, statement repairs, definition repairs, or consumer adaptations.

## Proved and sorry left

Closed 1 original hole:
`WeilConjectures.field_cohomology_perfect_descent_qbar`
(node `lem-sf-field-cohomology-perfect-descent`).

The module now contains zero `sorry`s. Added zero holes and split off zero statements.
`WeilConjectures.field_cohomology_perfect_descent_rational` was already proved and is retained.
The delivery uses existing stated dependencies, including their current proof assumptions,
so this is closure of this module's hole rather than a claim of axiom-free target closure.

## No longer needed

No existing Lean imports or modules are removed. The rational theorem still needs the
integral residue-Tor, dimension, integral-sections perfectness, small coefficient lift,
and rational model comparison dependencies.

For the qbar clause, repeating the integral-model construction is unnecessary: the existing
finite-dimensional bounded rational point fibres and the field-perfectness criterion give
the desired field models directly. The old `def-weil-derived-direct-image` proof dependency
is replaced by the directly used `def-weil-ordinary-compact-cohomology` object definitions;
its definitions remain transitively available and no source declaration is withdrawn.

Removed the obsolete `lem-weil-l-adic-integers-localization-uniformizer` entry from the
item's `tool_uses`: neither the existing rational proof nor the qbar proof directly uses
this theorem. The rational model comparison encapsulates the needed rationalization.
The signed dual scalar-calculus and projective Hom evaluation dependencies remain used.
No unit statement or realized unit step is bypassed (`sk-thm-sf-package` has no realized
node attachment for this item).

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The old qbar plan prescribed repeating
the integral construction, although its point-fibre interfaces already provide the precise
bounded finite-dimensional cohomology needed to apply the adopted source's proved field
perfectness criterion. This is a shorter route below the unit level, preserving the
stagewise geometric cohomology constructions and their signed duals.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
