# K4 purity transport audit

The assigned declaration is not proved. Its explicit statement and inherited binders are
unchanged from `19ba966718`. Merging Houyi #2087 moved the mathematical obligation to
`exists_natTrans_upperShriek_isIso_forget_of_smooth`; that theorem still has `sorry`.
No K4.DONE is warranted by this reduction.

## What the existing condensed purity gives

`SmoothPurity/Defs.lean:450` supplies `smoothPurityIso`, and
`TraceFormula/PurityCompatibility.lean` supplies the tensor formula for arbitrary coefficients.
These are geometric purity results. The chosen unit orientation is an isomorphism, but its
definition falls back to an arbitrary isomorphism when a canonical integral lift is unavailable
(`SmoothPurity/OrientationCanonical.lean:200`). That file explicitly says existence of the
compatible canonical lift has not been formalized.

`SmoothPurity/OrientationBaseChange.lean:121` supplies an existential Tate comparison. It does
not identify that comparison with the prescribed roots-of-unity pullback. Consequently it
cannot by itself prove the square with the native scalar cyclotomic Frobenius datum.

The `SmoothPurity/FrobeniusExchange/*` modules prove scalar evaluation and compact-support
exchange equations. Their exported statements do not identify the chosen purity orientation
or trace with the specified Tate datum.

## A way around canonical-orientation equivariance

Choose the existing smooth trace over the finite base field itself. Pulling it along
`geometricFiberWeilLowerStar` produces a morphism with its canonical Weil structure.
`boundedConstructibleLowerShriekGeometricFiberWeilIso` moves compact support past that pullback.
`SmoothPurityDescendedTrace.lean` implements exactly this construction and its base-change
identity. Its source is the pulled-back, roots-defined condensed Tate complex.

This avoids asking the arbitrarily chosen geometric orientation to commute with Frobenius.
It does not yet identify the trace's source with the native Tate twist, or prove that its
adjoint is invertible after geometric-fibre pullback.

## Remaining comparisons

1. Identify the pullback of the condensed roots-defined Tate line, with canonical Weil datum,
   with `ProEtaleWeilSheaf.toCondensed.obj (WeilSheaf.tateTwistSheaf ... d).obj`. The native line
   is defined by the scalar `cyclotomicUnit ^ d`, whereas the condensed line is a limit of free
   modules on roots of unity followed by extension of scalars. Relevant starting APIs are
   `upperStarMapModTateModuleIsoUnit`, `upperStarTateTwistIso`, and
   `upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison`. The missing
   calculation must identify geometric Frobenius on that trivialization with the cyclotomic
   scalar, first on every finite root projection, then on the limit and after scalar extension.
2. Show the adjoint of the descended trace is geometrically invertible, using exceptional
   base change and condensed purity. The field-extension comparison is a separate issue:
   `OrientationBaseChange` assumes all four schemes are finite type over the same field, so
   its direct instantiation with the algebraic closure does not apply. The
   `ModuleObject/DualizingFieldChange/*` modules are useful for the structural morphism.
3. Extend from the unit to all coefficients by a compatible projection formula, and transport
   through `CondensedModelWeilDerived` to the native Weil category. The specified native
   tensor comparison has to be respected here.
4. Handle the unchanged theorem's nonseparated base. The condensed bounded-constructible
   comparison APIs used above require schemes separated over the field; the assigned theorem
   only assumes the morphism `f` separated and the base quasi-separated.

## Shared Sheaf route

The apparent proof in `origin/iface-start` uses unfinished primitives. In particular:

- `lean/Sheaf/WeilSheaf/CondensedTatePairEncoding.lean`,
  `condensed_tate_pair_encoding`: `sorry`.
- `lean/Sheaf/WeilSheaf/CondensedUnitPurityCounit.lean:79`,
  `condensed_unit_purity_counit`: `sorry`.
- `lean/Sheaf/Paper/RationalWeilPurityNaturalityMate.lean:861`: `sorry`.
- `lean/Sheaf/Paper/IntegralEquivarianceMate.lean:79`: `sorry`.

These cannot be imported or ported as completed proofs. The blueprint explains the intended
finite-coefficient normalization, integral reconstruction, rationalization, and descent, but
does not replace these equations in Lean.

## Independent completed construction, awaiting remote checking

`SmoothPurityOpenImmersion.lean` proves zero Tate twist is the identity and the assigned
adjunction for open immersions, using the existing extension-by-zero adjunction. It does not
invoke general smooth purity. Neither new helper uses K2; K2's intended proof depends on K4,
so the reverse dependency must be avoided.

The direct consumers of K4 are the smooth dualizing-object theorem and, via K2, the affine-line
adjunction. The latter general API permits nonseparated bases; its concrete Fourier consumers
use separated affine spaces. This observation does not authorize changing the assigned
statement.
