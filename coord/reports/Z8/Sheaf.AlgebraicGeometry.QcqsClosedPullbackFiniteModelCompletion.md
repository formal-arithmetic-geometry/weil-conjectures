## What changed

Prove `AlgebraicGeometry.ProEtale.QcqsClosedPullback.finite_models_constructible_tor`
without changing its signature or any public definition. Private proved helpers assemble
point-model pullback, the pullback square comparison, preservation of finite models on
the specified cover, and preservation of constructibility through the actual pulled-back
stratification. The internal-module closed counit is obtained directly from the existing
abelian closed counit and the module/scalar adjunctions. The specified derived tensor
comparison then identifies tests against ordinary direct-image sheaves. Exact pullback
preserves the original homology interval, and its homology comparison preserves bounded
constructibility. No new postponed statements are introduced. All existing public signatures, definitions and
public imports are preserved verbatim. The geometric comparisons use abstract square
interfaces so the kernel does not unfold chosen scheme pullbacks inside module categories;
the derived argument retains the file's original elaboration settings.

Validation: the complete assigned module compiled cleanly through `lcompile.py` in
25.8 seconds, with no compiler warnings or errors. The delivery preflight is the final
packet and axiom check.

## Proved and sorry left

One of the two original direct holes is closed:
`AlgebraicGeometry.ProEtale.QcqsClosedPullback.finite_models_constructible_tor`.
No holes are added or split off. Its proof uses the existing derived tensor comparison;
that source-library comparison may still transitively depend on postponed proofs.

The one remaining direct hole is unchanged:
`AlgebraicGeometry.ProEtale.QcqsClosedPullback.normalized_strict_completion`
(node `lem-sfb-qcqs-closed-pullback-finite-model-completion`). The already proved
`derived_completion` still depends on it. This delivery makes no claim to close that
strict two-coordinate completion comparison.

## No longer needed

Removed these unused private proof imports (their public imports, if any, are unchanged):

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.Paper.PrincipalReductionDerivedNormalization`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`

The finite-model/Tor proof no longer directly requires these old node dependencies and
their tool-use approvals are removed:

- `lem-pur-scheme-constructible-preimage`
- `lem-weil-pbc-proetale-ringed-closed-counit`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-open-immersion-base-change`

The new route uses `lemma-constructible-pullback-stratification`,
`lem-zl-condensed-point-module-comparison`,
`lem-weil-pbc-proetale-abelian-closed-counit`, and
`lem-weil-pbc-exact-functor-bounded-below` through existing declarations.
The unfinished strict-completion theorem retains its planned mathematical dependencies
(including internal/section transport, product preservation, scalar matrices and principal
normalization); removing its unused imports does not claim to discharge or withdraw those
nodes. No module is withdrawn, and no adopted source declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. For finite scalar models, the existing point-pullback
comparison works for every module on the point, so no new finite-matrix calculation is
needed. Constructibility follows from the library's actual `Stratification.pullback`.
The abelian closed counit lifts directly through the module adjunction and the scalar
isomorphism; passing through sectionwise modules is unnecessary for this theorem.

Edge cases: all cover/stratum constructions retain their original index types and allow
empty indices and empty schemes. The zero ring and zero modules are included. The Tor
argument introduces no hypothesis `a ≤ b` and retains both endpoints verbatim, including
the zero-object case `a > b`. It tests against ordinary `i_*N` in degree zero, as required.
The integral definitions and their unbounded scope are unchanged.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
