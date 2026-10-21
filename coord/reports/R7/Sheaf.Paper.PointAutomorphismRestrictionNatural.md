## What changed

Filled `AlgebraicGeometry.ProEtale.point_automorphism_restriction_natural` in
`Sheaf.Paper.PointAutomorphismRestrictionNatural`, preserving its signature and all
existing definitions. Private proved helpers establish constant restriction, finite
normalization, quotient constants, finite projection equations, completed normalization,
and exact point sections in the independent coefficient universe.

The module transformation is constructed from the actual raw restriction maps. Mathlib's
termwise complex transformation and `Localization.liftNatTrans` give the specified
transformation on the entire unbounded derived category, with the required component equation.
The DAG proof, dependencies and proof origin now describe this implementation.

Added proof imports for affine ring-retraction evaluation, the w-local geometric
criterion, sheaf epimorphisms, and module epimorphisms. No public import or definition changed.

Validation: the delivered module passed standalone `lcompile.py` in 17.3 seconds,
with no warnings.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.point_automorphism_restriction_natural`
(node `lem-weil-point-automorphism-restriction-natural`).

Holes added: zero. Holes left in the item: zero. No statements split off.
Existing imported theorem holes remain their own items; in particular the constructed
completed coefficient comparison uses its recorded invertibility theorem.

## No longer needed

Removed the proof-only import `Mathlib.CategoryTheory.Sites.Pullback`.
The proof uses the sectionwise comparison's existing constant normalization directly,
so it does not invoke `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`
or a fresh colimit/coprojection calculation through `def-weil-proetale-inverse-image`.
The canonical coordinates and coprojection identification remain those already supplied
by the statement's definitions and `lem-weil-proetale-isomorphism-inverse-image`.

The proof does not apply `lem-weil-point-proetale-sections-exact` directly: its recorded
signature fixes the coefficient universe to the field universe plus one. Instead it uses
the existing geometric criterion and affine ring-retraction evaluation theorem, whose
universes support the exactness needed here. Removed the two obsolete tool approvals for
this point-sections theorem and the pullback-adjunction theorem from this node's `tool_uses`.
The pre-existing public import of `Sheaf.Paper.PointProEtaleSectionsExact` is preserved;
no global module withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The proposed direct application of `point_proEtale_sections_exact` cannot cover
independent field and coefficient universes. Its mathematical argument does generalize:
the private helper repeats its elementary field calculation, applies the already general
ring-retraction evaluation theorem, and derives exactness through the reflecting
forgetful functors. The statement and its geometric restriction/localization route are
unchanged. The two existing lower results are used as tools, without changing any unit
statement or step.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
