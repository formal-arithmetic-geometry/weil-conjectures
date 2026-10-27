## What changed

Filled `WeilConjectures.frobeniusFixedPairComparison` from the three existing declared
proof dependencies: `geometric_fibre_comparison_hypotheses`,
`IsoAlgebra.fixedPair_equivalence_transport`, and `IsoAlgebra.fixedPair_mixedSquare_lift`.
Added private proved helpers for endpoint transport, heterogeneous component equalities,
and the reverse-oriented mixed-square calculation. The public signatures and definitions
are unchanged. Local irreducibility annotations on scalar localization, derived pullback,
coefficient, and derived-category constructions prevent expansion during proof
elaboration. Local stage-category projection annotations follow existing common-stage
proofs. The same technique is already used by `DerivedPullbackTensorHom`. A private
generic stage-system lemma checks the scalar and inclusion calculations once before their
specialization to the supplied system. Updated the item node's proof description to match
this assembly.

The complete module passed `lcompile.py` in 19.5 seconds. The key normalization is
`dsimp only at h₂`: it reduces the literal pair's stage projection before matching
inclusion maps, avoiding expansion of their quotient implementation. Profiling options
and scratch modules were removed before delivery.

The finite comparisons are transported along the explicit equality of the two rational
stage categories and the heterogeneous fields `finite_functor` and `sfFinite`. The category
equality is checked from the identical small coefficient models, field and algebra
structures, following the private construction in `PurFrameworkPbcCoefficientCategoryComparison`.
The common comparison is transported along `pair_functor` and `sfPair`. These are equality
transports of the supplied isomorphisms, as verified by HEq, rather than new choices. The scalar square
is exactly the expanded `mixed.comm` equation. The inclusion square follows from
`pair_components` and the identity components of `iotaCompFunctorIso`. Finally the
framework Weil categories are identified with the actual fixed-pair source categories
using uniqueness of the invertibility instances. No coefficient or pullback data is
chosen from an existence statement.

The three searches ran through msearch.py (Lean Finder, Loogle, Mathlib grep); the existing
project declarations are the applicable results. The current blueprint's trace definition
is now under `sk-cor-plancherel`; its local Frobenius/Weil-structure content is unchanged.
The item's unit record has no realized steps to bypass, and all three planned proof
branches are retained.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.frobeniusFixedPairComparison`
(node `lem-fd-frobenius-fixed-pair-comparison`). No holes added or split off. No `sorry`
remains in any delivered Lean file. The existing three dependency modules are used with
their existing declarations; this delivery does not claim to close their transitive holes.

## No longer needed

Removed the old private proof imports `Sheaf.Paper.FdCoefficientComparison`,
`Mathlib.AlgebraicGeometry.Noetherian`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
`Mathlib.CategoryTheory.Equivalence`. The new dependency imports provide the declarations
needed by the assembly. All public imports are preserved.

All three planned proof dependencies are retained. The item no longer directly needs the
dimension lemma `lem-kun-dimension-finite-type`: the geometric-fibre hypothesis theorem
already encapsulates that argument. The dimension lemma remains needed inside that
theorem, so the existing tool approval is preserved. No module or declaration is withdrawn
or globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The rework table retains an older quarantine
entry, but the current item source is present and is preserved, including all public
imports and declarations. No return entry for this item is present. The latest blueprint
moved the trace definition from the historical `sk-def-trace` folder to
`sk-cor-plancherel`; the source was read at its current location.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
