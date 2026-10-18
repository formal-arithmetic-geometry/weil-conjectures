## What changed

Proved `AlgebraicGeometry.Etale.finite_directImage_constructible_and_higher_vanishing`
in `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage`, without changing its signature.
Updated its docstring and DAG proof to the compiled argument. No definitions or statements changed.

Constructibility follows by forgetting to sets, applying the assigned Noetherian finite abelian
pushforward theorem, recovering module constructibility with the finite-coefficient theorem at
I = 0, and applying the existing constructibility comparison. Direct-image/forget compatibility
is definitional for the coefficient-valued sheaf functors actually in this statement.
Higher vanishing uses the generic finite-direct-image exactness instance with ModuleCat coefficients,
the bounded below exact-functor comparison, and homology of F concentrated in degree zero.

Compilation through lcompile.py passed cleanly in 5.0 seconds. The statement works without choosing
any witness from an unproved existence theorem. Zero coefficient rings, empty schemes and the zero
sheaf need no special case: the existing constructibility lemmas explicitly cover them, the quotient
map is surjective in every case, and the homology argument only uses 0 < q.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.finite_directImage_constructible_and_higher_vanishing`
(node `lem-fin-finite-morphism`).
Added 0 holes, split off 0 statements. There are no sorries left in the item or added by this delivery.
Existing dependencies retain their own proof status; this is a proof from existing declarations.

## No longer needed

Removed proof imports:
- `Mathlib.AlgebraicGeometry.Noetherian` (replaced by the source library Noetherian API).
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`.
- `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (available through statement imports).
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` (the existing source predicate suffices).

The proof no longer directly needs nodes `def-weil-pbc-constructible-abelian-sheaf`,
`lem-weil-pbc-module-direct-image-left-exact`,
`lem-weil-pbc-constant-sheaf-sections-locally-constant`,
`def-weil-sheaf-of-modules-category`, or `lem-weil-pbc-etale-composition-cancellation`.
Their modules above are unnecessary direct proof imports. The constructible-module refinement is
reused through its existing theorem, instead of repeating its action-table argument here.
The coefficient convention and constructible-module predicate remain in the statement interface.
Removed the obsolete top-level tool approvals for module direct-image left exactness and constant
sections. No blueprint unit statement or realized proof step is bypassed: the unit record has no
realized entries, and the finite-pushforward constructibility argument is retained.

## Where the brief, the DAG or earlier work was wrong

The planned module-to-abelian exactness transfer is unnecessary: the existing finite-direct-image
exactness instance is already generic and applies to ModuleCat Lambda. The planned action-table
refinement is already packaged in `isConstructibleSheaf_of_finite_coefficient_underlying_sets`.

Reused three existing generic tools from unit sk-thm-p1:
`lem-weil-pbc-constructible-module-underlying-sets`,
`lem-weil-pbc-constructible-module-of-finite-coefficient-sets`, and
`lem-weil-pbc-constructible-etale-module-sheaf-comparison`. They supply respectively the forgetful
constructibility, finite operation-table refinement, and equivalence of the two existing module
predicates. The assigned unit has no alternate declaration packaging those operations. These are
existing nodes, not new split-offs; their use follows the same mathematical proof as the item.
No tool approvals were added by the worker; independent review can register them if required.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
