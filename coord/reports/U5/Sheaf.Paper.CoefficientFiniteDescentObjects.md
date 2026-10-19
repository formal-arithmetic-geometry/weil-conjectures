## What changed

Proved `AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects` with its original
signature. Finite type over a field supplies the Noetherian instance. The proof translates
the finite-constant-model predicate to upstream bounded constructibility, applies
`constructibleCocone_essSurjObj`, and translates the resulting finite model back. Enlargement
uses `boundedConstructible_derivedExtendScalarsSubfield_obj` and the specified
`derivedExtendScalarsCompIso`, composed with the given model isomorphism.

Added and proved `Sheaf.Paper.ConstantModelBoundedConstructibleComparison`. The retained
attempt had left its comparison theorem as `sorry`. An existing private proof in downstream
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit` gives the missing argument, but importing
that module would form a cycle. The new module reuses that argument with the lower
local-freeness and coefficient-transport proofs of
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` (via `import all`). No downstream
module is adapted. No statement, definition, or target is changed. The parent and new node
now record the proof actually written.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects`
(node `det-lem-coefficient-finite-descent-objects`): 1 of 1 original sorries proved.
Also proved the retained helper
`AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_eq_boundedConstructible`
(node `lem-coefficient-finite-descent-predicate-comparison`). All private helpers are proved.

Sorries left in delivered modules: none. Holes added: zero. Split-offs left: zero.
The imported inputs may themselves depend on their recorded open obligations, as intended
for stage 3. Both sandbox modules compile without errors or warnings. The two direct consumers,
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit` and
`Sheaf.SixFunctors.IntegralModelsGenerators`, also compile unchanged against the sandbox
artifacts (51.5 s and 20.7 s respectively).

The comparison uses the same finite stratification in both directions. Noetherianity is
used on each stratum before invoking coefficient-specific local freeness; it does not assert
the false unrestricted converse for arbitrary schemes or coefficient rings. Empty schemes,
empty strata, rank zero, K = 0, and F = E need no nonemptiness or strict-inclusion assumptions.

## No longer needed

Removed direct imports of:

- `Mathlib.AlgebraicGeometry.Noetherian` (replaced by the finite-type Noetherian API in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`);
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`;
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`;
- `Sheaf.Paper.CoefficientFiniteDescentHom`;
- `Sheaf.Paper.CoefficientFiniteDescentLisse`;
- `Sheaf.Paper.CoefficientHeartGeneration`;
- `Sheaf.Paper.CoefficientHeartTriangulated`;
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`;
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` (its public
  declarations already come through the retained statement import of `TwoColimit`);
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.

The parent no longer directly needs the old planned dependencies
`sk-def-sfb-dc-setting`, `lem-weil-pbc-exact-functor-derived-factorization`,
`lem-sfb-subfield-flat`, `lem-sfb-qlbar-flat`, `det-cor-coefficient-heart-ii-triangulated`,
`def-weil-finite-subextension-directed-set`, `sk-def-sfb-change-of-scalars`,
`def-sfb-derived-extend-to-qlbar`, `sk-def-sfb-derived-categories`,
`det-lem-coefficient-finite-descent-hom`, `def-weil-triangulated-category`,
`lem-sf-triangle-morphism-iso`, `det-lem-coefficient-finite-descent-lisse`,
`det-cor-coefficient-heart-ii-generation`, and `det-prop-scalar-six-pullback`.
The upstream object-descent and preservation proofs already package their cone and lisse
arguments. Some remain reachable through other modules or as statement dependencies; no
claim is made that all of these modules disappear from the global targets' closure.
The obsolete `det-prop-scalar-six-pullback` entry is removed from the parent node's
`tool_uses`, because the written proof does not use that comparison. The unit record has
empty realized step lists, and no unit statement or step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the predicate comparison open and its node gave only the informal
phrase "finite presentations over a field are finite free". For sheaves with continuous
coefficients, the converse needs the existing Noetherian-base local-freeness theorems and
transport through Cartesian coefficient isomorphisms. This delivery supplies that Lean
argument. The direct five-step cone plan need not be repeated because
`constructibleCocone_essSurjObj` already proves its upstream form.

## New nodes

`lem-coefficient-finite-descent-predicate-comparison`, in
`lean/Sheaf/Paper/ConstantModelBoundedConstructibleComparison.lean`, is fully proved from
finite constant models implying local finite presentation, the finite-field and
algebraic-closure local-freeness inputs on Noetherian strata, and preservation of finite
free regular modules by coefficient inverse image. It adds no new obligation. Its node
records these dependencies and the successful three kinds of Mathlib search. Import pruning is recorded in
`coord/changes/coefficient-finite-descent-objects-import-pruning.md`; all existing
signatures and definitions are unchanged.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
