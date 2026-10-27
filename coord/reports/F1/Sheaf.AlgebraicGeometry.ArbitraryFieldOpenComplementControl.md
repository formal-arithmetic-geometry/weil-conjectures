## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.exists_uniform_dimension_bound_and_hasOpenComplementCondition`
in `Sheaf.AlgebraicGeometry.ArbitraryFieldOpenComplementControl` with the four-step
argument recorded in its existing node. Finite-type composition supplies the uniform
field-extension dimension bound. Multiplication by the positive annihilator makes every
section of the underlying abelian sheaf torsion; the quantitative torsion vanishing theorem
and the coefficient-forgetting comparison then give vanishing for arbitrary module sheaves.
Faithfulness of the forgetful functor reflects zero objects. A constructible sheaf placed
in degree zero is bounded constructible; finite-type direct-image constructibility and the
bounded-below comparison give constructibility in every integer degree.

Added two proof-only imports:
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
The existing statement, public imports, definitions, and planned DAG route are unchanged.
No other module was modified. The argument applies to every admissible dimension bound,
allows empty schemes and the zero coefficient ring, and assumes no separable closedness
or absolute cohomological-dimension bound on the ground field.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_uniform_dimension_bound_and_hasOpenComplementCondition`
(node `lem-pur-etale-arbitrary-field-open-complement-control`).

One of one original holes closed; zero holes remain in the item; zero holes added;
zero statements split off. The proof uses the existing declared dependencies as intended
by stage 3. Validation: the item compiles through `lcompile.py`; delivery runs the server
preflight and axiom/declaration checks.

## No longer needed

None. All original imports and declared proof dependencies are used. No module or node
is withdrawn or pruned, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The original imports omitted two proof APIs used
for the planned constructibility step: equivalence of the finite-value and finite-stalk
constructibility predicates, and compatibility of the unbounded and bounded-below right
derived functors. These are supplied by the two added private proof imports.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
