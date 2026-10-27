## What changed

Filled seven auxiliary proof bodies in `Sheaf.Paper.CondensedTateIntegralTower`,
without changing any existing statement, definition body, instance signature,
or public import. The proofs use the concrete p-adic quotient equivalence,
the existing perfect-module theorem over a PID, the associated-module
realization equivalence, the theorem on inverse mates across equivalences,
and the universal property of limits.

Private proved helpers establish the residue equations and compatibility of
all quotient maps, and the naturality of the finite coefficient comparisons.
The node records these dependencies alongside the retained plan for the main
reconstruction theorem. No other Lean module is changed.

Validation: `lcompile.py` compiled the complete module with no errors or warnings
in 35.4 seconds after factoring the generic limit uniqueness proof into a
proved private helper. An earlier delivery attempt pushed nothing because its
compile timed out; this proof refactor reduces repeated checking of large
coefficient sheaf expressions. All original declaration signatures and public imports are
preserved; the only remaining `sorry` is the original main theorem.

## Proved and sorry left

The original module had eight holes. Closed seven, all in
`AlgebraicGeometry.Scheme.PurityIntegralTower`:

- `coefficientProperties`;
- `residueIso_existsUnique`;
- `scalars_locallyBijective`;
- `realization_exact`;
- `scalars_comp`;
- `scalarComparisonMap_isIso`;
- `completionIso_existsUnique`.

One original hole remains: `condensedTateIntegralTower`, at node
`lem-pur-condensed-tate-integral-tower`. Its complete original statement and
proof plan are retained. In particular, this delivery does not claim to
construct its normalized strict Tate towers, uniform local models, compatible
origins, or exceptional comparison square.

Added zero holes; split off zero statements. This is a partial delivery of
seven proved auxiliary claims, not a decomposition of the main theorem.

## No longer needed

Removed these unused private proof imports from this module:

- `Mathlib.RingTheory.NoetherNormalization`;
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`;
- `Sheaf.Paper.TateTwistLocallyFree`;
- `Sheaf.Paper.ConstantCompletionEquivalence`;
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`;
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`;
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`;
- `Sheaf.Paper.NormalizedEtaleOriginWitnesses`.

None is used by the seven completed proofs. No node or module withdrawal is
claimed: the main reconstruction theorem remains open, and the dependencies
of its eight-step plan are retained in the DAG. All original public imports
are preserved. No adopted source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. For the auxiliary claims there are shorter
existing routes: the PID-model theorem supplies perfectness directly, and
the inverse-mate theorem supplies invertibility of the precise scalar mate.
The DAG now explicitly records these routes. The main reconstruction claim
still needs the geometric and common-model arguments in its existing plan.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
