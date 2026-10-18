## What changed

Proved `AlgebraicGeometry.Etale.isBoundedConstructible_of_finite_rightDerivedLowerStar`
in `Sheaf.AlgebraicGeometry.FiniteReflectsBoundedConstructible`, with its signature and
public imports unchanged. The proof uses the source library's proved exact-functor
cohomology comparison for finite module direct image, transports constructibility
along that comparison, applies the declared sheaf-level finite reflection theorem,
and reflects zero cohomology outside exactly the original interval.

Added one proved private helper `constructible_of_iso`: it retains the stratification,
covers and finite module values and composes the trivializations with the restricted
isomorphism. Added the proof import `WeilConjectures.SixFunctors.Finite.Counit`.
Updated the existing node's proof route and proof dependencies to describe this code.
No statements, definitions or consumer modules changed; no change record is needed.

Validation: the complete module compiled through lcompile.py without errors or warnings.
The proof applies to the unbounded derived category and makes no bounded-below assumption.
The same witnesses work for empty schemes, nonsurjective finite morphisms and the zero
coefficient ring. No arbitrary object is selected from an unproved existence theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isBoundedConstructible_of_finite_rightDerivedLowerStar`
(node `lem-fin-finite-reflects-derived`). Added 0 holes, split off 0 theorems.
There are no remaining sorry declarations in this delivery.

The existing dependency
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_finite_lowerStar`
(node `lem-fin-finite-reflects-constructibility`) is still unproved in its own module;
this delivery proves the assigned theorem from that declared dependency, as required.

## No longer needed

Removed the following proof imports:

- `Sheaf.CategoryTheory.RingedSiteModules`:
  `def-weil-sheaf-of-modules-category` is unnecessary because finite exactness is already
  proved directly for the ModuleCat-valued sheaves used by the statement.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`:
  `lem-weil-pbc-exact-functor-derived-functor` is unnecessary; the source library already
  proves `rightDerivedFunctorHomologyFunctorIso` on unbounded derived categories.
  Removed the obsolete top-level tool approval for this unused dependency.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: the proved comparison API
  is provided through the source finite exactness module.
- `WeilConjectures.SixFunctors.Finite.Stalk` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`: their zero-reflection
  argument is already packaged by the new Counit import. The corresponding nodes remain
  mathematical proof dependencies of that argument.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`: already publicly
  re-exported by the existing signature import of its Sheaf compatibility module.
- `WeilConjectures.SixFunctors.Finite.Exact`: replaced by its importing module
  `WeilConjectures.SixFunctors.Finite.Counit`, which supplies both exactness and
  zero-reflection. Its exactness node remains needed.

No separate zero-sheaf constructibility argument is needed: the input predicate
already gives constructibility in every degree. No unit statement or unit proof step
is bypassed (the unit record has no realized nodes). No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proof plan predates proved source-library APIs for unbounded exact-functor
cohomology and finite direct-image reflection of zero objects. Reusing them removes
the ringed-site encoding detour and the generic unproved derived-functor dependency.
The mathematical statement and its three-step route are correct and unchanged.
The plan's final distinction between degrees inside and outside the interval is
unnecessary because the recorded predicate provides constructibility in all degrees.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
