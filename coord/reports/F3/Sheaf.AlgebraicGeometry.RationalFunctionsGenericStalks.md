## What changed

Proved `AlgebraicGeometry.Scheme.rationalFunctions_generic_stalks` in
`Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks`, preserving its full signature.
Two proved private helpers construct disjoint component opens and prove density of an open
containing every generic point. The germ cocone induces a ring homomorphism from the colimit;
filtered-colimit representatives and sheaf locality prove injectivity, and disjoint gluing of
stalk representatives proves surjectivity. The integral clause uses singleton components,
product evaluation, and Mathlib's generic-stalk field theorem.

The existing node's proof now records the actual equality-of-representatives argument and
Mathlib APIs. No definitions, public statements, or consumers changed. Single-file compilation
passed without warnings in 6.9 seconds before removal of redundant imports; the delivery dry
run verifies the final file and all declaration axioms.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.rationalFunctions_generic_stalks`
(node `lem-sc-rational-functions-generic-stalks`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean module.
The proof uses no project theorem containing `sorry`; its ingredients are Mathlib and the
existing actual dense-open diagram and colimit definitions.

The proof handles `n = 0` without choosing an index: the empty family covers the empty scheme,
the locality and gluing APIs include the empty cover, and the integral branch separately
constructs an index from the component of the whole nonempty irreducible scheme. Universes
remain arbitrary as in the original theorem.

## No longer needed

Removed proof imports `Sheaf.Topology.PresheafModuleStalkFunctor` and
`WeilConjectures.Topology.PresheafModuleStalkFunctor`. Only the existing ring stalk and germ API
is used, already available through the public Mathlib imports; the presheaf-of-modules stalk
functor is unnecessary. The conceptual dependency `def-weil-pbc-module-stalk` remains because
its ring-stalk representation and equality clauses are used.

The added exploratory imports `Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` were also removed: both are already
publicly imported by `Mathlib.AlgebraicGeometry.Properties` through its dependencies.

Removed `lem-sc-scheme-sober` from the proof dependencies and step 1 uses. The generic points
are supplied in the theorem's hypotheses, so their existence and uniqueness are not used.
Its statement dependency remains unchanged. The affine fraction-ring API in
`lem-sc-integral-function-field-affine-fraction` is unnecessary beyond its generic-stalk field
clause, supplied directly by Mathlib's
`AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents`.
All other declared dependencies remain relevant; no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The proof plan's injectivity argument can be simplified:
compare arbitrary representatives on a dense union of equality neighborhoods, without
shrinking these neighborhoods into the disjoint component opens. Disjointness is needed only
for surjectivity. Sobriety and the module-valued stalk functors are not required when the
generic points and their genericity proofs are explicit hypotheses. The supplied unit record
`sk-def-av-pic` has no realized statement or proof-step requirement for this lemma.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
