## What changed

Proved all four declarations in `Sheaf.Paper.FiniteCoefficientFlatModel` without changing
their signatures. The pro-etale proof works in the recorded constant-ring module category,
using the existing independent-universe flat-resolution construction. It identifies the
site tensor with categorical tensor, converts acyclic-tensor K-flatness to categorical
K-flatness, and compares every explicit derived tensor model with the categorical derived
tensor. This identifies the two amplitude predicates for the given ordered interval.
The existing generic bounded-flat-model theorem then gives exactly the requested model.
Its proof uses the unit's bounded-above flat resolution and lower good truncation.

The etale equivalence converts finite-value bounded constructibility to the source
predicate through the proved constructible-sheaf comparison. The Noetherian variant
applies the existing finite-value constructible-model theorem and reverses the model
isomorphism. The final existence theorem unpacks its Tor interval and applies that variant.
Both etale proofs install finiteness of the coefficient quotient and its universe lift.

Added proof-only imports of `Sheaf.Algebra.Homology.KFlatResolutionGeneral` (with `all`
to access its already-proved private category/resolution helpers),
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`, and
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
The DAG proof now records this direct ringed-site argument and its actual dependencies.
Tensor objects and isomorphisms use qualified names in the pro-etale proof, so the
original module scopes are unchanged.
No definition, public import, target statement, other module, or new theorem is changed.

Validation: the complete retained module compiles against the published library in
13.4 seconds with no warnings (rechecked on 2026-10-19). The current source comparison confirms unchanged
statements, four original holes closed, and no new holes.

## Proved and sorry left

Closed the four original holes, all attached to node `lem-sf-flat-model`:

- `AlgebraicGeometry.Scheme.finiteCoefficient_torAmplitude_iff_flatModel`.
- `AlgebraicGeometry.Etale.finiteCoefficient_hasTorAmplitude_iff_flatModel`.
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_flatConstructibleModel`.
- `AlgebraicGeometry.Etale.finiteCoefficient_exists_boundedFlatConstructibleModel`.

No `sorry` remains in the item. No holes or split-off statements were added.
The result is a proof from existing declarations, not a decomposition.

## No longer needed

The pro-etale proof does not use `lem-sf-proetale-flat-model` or its module
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FlatModel`.
It does not require identification with etale-origin bounded constructibility,
`lem-sf-proetale-constructible-origin`, or a coefficient-category equivalence.
These are unnecessary for this proof, without asserting that they are globally unreached.
The DAG removes `lem-sf-proetale-flat-model` from `proof_deps`; its existing `stmt_deps`
entry is retained because this delivery changes only the proof route.

Removed these unused proof-only imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.

The retained public imports supply the existing statement interface. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old DAG step called the categorical pro-etale theorem an exact match. As already noted
in that dependency's `statement_change.citers`, it uses a different category and a different
constructibility predicate. The item itself is unchanged. Specializing the generic source
flat-model argument directly to the recorded ringed-site category avoids this mismatch.
The intrinsic constructibility and global arithmetic hypotheses are unnecessary for that
generic pro-etale argument, but all are retained in the theorem signature.

The generic flat-model node `lem-sc-source-tor-amplitude-flat-model` is used as a proved
tool: its source theorem implements exactly this unit's flat-resolution/truncation route.
The tensor comparison node `lem-weil-pbc-independent-sheaf-tensor-colimits` and the
K-flat-resolution node `lem-pc-kflat-resolution` supply general ringed-site tools, not a
replacement for any unit step. All helper proofs imported with `all` are already proved.

Edge cases retain the same argument: empty schemes, zero rings and zero complexes are
handled by categorical zero objects; degenerate intervals `a = b` use the same generic
model theorem; positive coefficient levels are used precisely for the etale finiteness
instances. No new statement requires an edge-case audit.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
