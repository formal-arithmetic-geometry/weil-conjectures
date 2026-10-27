## What changed

Replaced the hole in `normalizedTower_lisse_of_native_strata` with induction on the
successive finite quotients. Restriction along the actual level coefficient isomorphisms
commutes with derived extension by an explicit adjunction comparison. Normalization
identifies each reduced level with the preceding one. The quotient transition is
surjective with square-zero kernel, and the final pullback/restriction homology
comparison recovers exactly the original conclusion.

Added `FiniteNativeRelativeLisse`: a complete proof that the supplied native finite
models give relative finite lissity even for an arbitrary coefficient isomorphism.
It reuses the proved finite-underlying-model and relative/fixed-model comparisons
through proof-only `import all` imports.

Added `RelativeNilpotentLissity`: a proof from the already proved
`SheafOfModules.lisse_of_nilpotent_coefficient_surjection` and the small-site comparison
below. Added `RelativeFiniteCoefficientModel` to isolate that remaining comparison.
The existing statement, definition, and public imports are unchanged. No other existing
Lean module was edited.

Validation: the four modules compiled together in import order. The finite-native
helper took 35.3 s, the comparison statement 13.5 s, the nilpotent application
43.9 s, and the assigned module 46.8 s; each is below 60 s. The first delivery
check compiled all four again, but refused an unused-variable warning for `hab`.
The bound now uses `max a b`, simplified using `hab`, to reference this original
hypothesis explicitly without changing the statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.normalizedTower_lisse_of_native_strata` by a complete Lean
proof from the stated intermediate results. The induction, kernel calculation,
coefficient-extension naturality, exact homology comparisons, and combination of
the intermediate results contain no holes.

The new theorem `AlgebraicGeometry.Scheme.finite_native_models_relative_lisse` is
proved without a hole. The new theorem
`AlgebraicGeometry.Scheme.relative_finite_lisse_of_nilpotent_reduction` is proved from
the existing nilpotent coefficient theorem and the remaining comparison.

The only remaining/new hole is
`AlgebraicGeometry.Scheme.exists_relative_finite_coefficient_model`, node
`lem-weil-pbc-relative-finite-coefficient-model`. It asserts preservation of zero
cohomology and identification of two lissity predicates under exact small-site
coefficient encoding and scalar extension. It assumes neither nilpotence nor
surjectivity, nor any lissity or boundedness hypothesis, and asserts no propagation
of lissity. Its docstring gives the construction and the slice/scalar comparisons.
The module includes zero rings and empty schemes; there is no choice of data from
an unproved theorem in a definition.

This is a decomposition: one original hole closed, one new hole added, net zero
holes removed. The small-site/coefficient-encoding glue remains to be formalized;
the nilpotent theorem itself is reused rather than restated with a hole.

## No longer needed

No modules are withdrawn or claimed globally prunable. No original imports were
removed. The original direct DAG dependency on
`lem-weil-pbc-nilpotent-reduction-lissity` is now indirect through the already proved
`lem-sfb-nilpotent-coefficient-lissity`; it remains needed and is not pruned.
The ring-sheaf change adjunction remains a direct dependency.

The route uses consecutive square-zero quotient maps rather than constructing the
single ideal in every quotient with quotient the first level. Consequently this
proof does not need the parent's private `quotient_factor_equiv` or
`quotient_factor_equiv_mk` constructions. Their parent module is still needed, and
no deletion is proposed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. Two comparison details must be explicit. First, the
native hypothesis supplies an arbitrary coefficient isomorphism, so a proof only
for the canonical constant-section isomorphism does not suffice; the proved
finite-underlying-set argument handles this. Second, the nilpotent-lissity theorem
uses a site whose object, morphism, and coefficient universes agree, while the native
pro-etale site has different object and morphism universes. Its direct application
there is ill-typed. The remaining comparison passes to the equivalent AsSmall site
and explicitly compares scalar extension as well as local models.

The native/small comparison imports also expose integral-coefficient sheafification
aliases with an independent coefficient universe. Instance tracing showed that the
local-bijectivity alias left a max-universe parameter undetermined on the native
site. The two new comparison declarations locally disable those three aliases for
their own elaboration, following existing library proofs; no global instance
attribute or existing module is changed.

## New nodes

`lem-weil-pbc-finite-native-relative-lisse` records the proved finite-native-model
transport in `Sheaf.Paper.FiniteNativeRelativeLisse`.

`lem-weil-pbc-relative-nilpotent-lissity` records the proved application of the
existing nilpotent coefficient theorem in `Sheaf.Paper.RelativeNilpotentLissity`.

`lem-weil-pbc-relative-finite-coefficient-model` records the sole remaining
small-site and coefficient-encoding comparison in
`Sheaf.Paper.RelativeFiniteCoefficientModel`. This is a transport step of the
original plan, not the tower propagation statement under another name.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
