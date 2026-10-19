## What changed

Completed `AlgebraicGeometry.Etale.qcqs_higherDirectImage` with its signature unchanged.
The ordinary-sheaf clause uses the proved source-library
`AlgebraicGeometry.higherDirectImageSheafifiedPresheaf`. For the arbitrary K-injective
representative, exact precomposition identifies the underlying presheaf homology;
exact sheafification and its counit recover the pushforward complex's homology.
The K-injective computation and bounded-below/unbounded compatibility identify that
homology with the required derived direct image. Updated the declaration docstring
and the existing node's proof, proof dependencies, proof origin, and obsolete tool approval.
Added only three plain proof imports; all public imports and signatures are unchanged.
No new module, definition, statement, or assumption was introduced.

Validation: the complete proof compiles cleanly through lcompile.py in 3.6 seconds.
The construction handles every integer q, the zero complex, the identity map and
empty schemes uniformly. No strict boundedness or termwise injectivity is imposed on I.
The item's node is not a unit-realization node; the unit route is preserved.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.Etale.qcqs_higherDirectImage`
(node `lem-weil-pbc-qcqs-higher-direct-image`). Both conjuncts are proved.
Holes closed: 1. Holes added: 0. Holes remaining in the delivery: 0.
No decomposition or split-off theorem.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`

Removed these declared proof dependencies from this item's route:

- `prop-weil-pbc-kinjective-resolutions-exist`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `def-weil-pbc-etale-sum-extension`
- `lem-weil-pbc-etale-restriction-injectives`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `def-weil-pbc-etale-cohomology`
- `prop-weil-pbc-cohomology-resolution-independent`

The chosen representative is already supplied by the second clause, so no resolution
existence theorem is needed. The actual statement uses the presheaf complex directly;
therefore restriction preserving injectives/K-injectives and a separate comparison with
restricted global cohomology are unnecessary. The first clause already has a proved
library formula. The two source modules for derived homology computations replace
these intermediate arguments. Removed the obsolete
`prop-weil-pbc-kinjective-resolutions-exist` entry from `tool_uses`.
These are dependencies pruned from this item; no claim is made that other targets
cease to use them, and no existing Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous plan expands restriction, extension by zero, and resolution independence,
although the landed first-clause formula and the stated sectionwise second clause
admit the shorter proof above. No mathematical statement was found false or changed.
The source's proved compatibility theorem
`src-right-derived-functor-plus-compatibility` is used as an existing closed tool;
its source module is imported privately for the proof. No change record is needed:
only proof code, private imports, and the permitted DAG proof fields changed.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
