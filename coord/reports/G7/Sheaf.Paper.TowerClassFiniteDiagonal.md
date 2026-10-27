## What changed

Filled both theorem proofs in `Sheaf.Paper.TowerClassFiniteDiagonal`, preserving every
existing signature, instance and public import. Added the public import
`Sheaf.Paper.SingleBoundaryNormalization` for the generic predicate used by the definition. The exactness argument uses finite
pro-etale direct-image exactness, finite presentation of the diagonal of the smooth
projective line, and detection of exactness by the jointly faithful evaluation functors.
Its general coefficient-system step is proved in `Sheaf.Paper.ClosedTowerDirectImageExact`.

Constructed the supported quotient by pushing forward the existing `finiteQuotient`
and composing with the inverse of the ordinary direct-image evaluation comparison.
Its prescribed values follow from the existing finite quotient's generator formula.
Uniqueness applies `Sheaf.Paper.ClosedIntegralHomExt`: cancel the epimorphism from the
ambient constant integer sheaf, then use the sheafification universal property on
constant generators. The evaluation comparison is an isomorphism, so equality after
applying its section map implies equality before applying it.

The epimorphism is proved in `Sheaf.Paper.DiagonalIntegralUnitEpi`. A locally constant
integer function on a closed subspace extends locally to the ambient chart. The existing
constant-sheaf/continuous-function comparison identifies restriction with the canonical
constant direct-image map. This works on arbitrary charts, including empty charts, without
quasi-compactness or finite coefficients. All three new helper theorems are proved.

Refactored `FiniteDiagonalNormalization` using four local let bindings and the existing
`evaluatedDiagonal` arrow. Zeta reduction and unfolding `evaluatedDiagonal` and
`forgetEvaluatedArrow` and `singleBoundaryEquality` give identical bodies, preserving the
normalization and public type. The new generic predicate forms single-complex and shift
witnesses before specializing to the large coefficient sheaves. Profiling
had located 45--54 seconds of kernel type checking in this definition. After sharing its
arguments, extracted the proved general exactness and generator-extensionality steps into
separate modules to meet the per-file limit. Private comparison lemmas avoid repeatedly
unfolding the large coefficient construction. Updated the item's DAG and added helper nodes.
The change record is `coord/changes/g7-finite-diagonal-normalization-sharing.md`.
No other existing module was changed.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.diagonalPush_exact`;
- `AlgebraicGeometry.ProEtale.SpTowerClasses.finiteSupportedQuotient_existsUnique`.

Both are attached to `def-sp-tower-class-finite-diagonal`. The new proved theorems are
`AlgebraicGeometry.ProEtale.SpTowerClasses.closedIntegralUnit_epi`,
`AlgebraicGeometry.ProEtale.SpTowerClasses.closedIntegral_hom_ext`, and
`AlgebraicGeometry.ProEtale.SpTowerClasses.closedTowerPush_exact`, with nodes listed below.
No `sorry` remains in any of the five delivered Lean files. No holes are added or split off.
Validation: `lcompile.py --all` compiled all five delivery modules and the unchanged
`Sheaf.Paper.SmoothPurityTowerClasses` consumer successfully (exit 0), with no errors or
warnings. Every file was accepted by the service's per-file limit. The unchanged consumer
copy was removed after validation. No profiler or trace options remain.

## No longer needed

None. The item's original public import remains necessary. Its DAG had no original proof
dependencies to prune, and all three statement dependencies remain needed. Finite-level
exactness and integral generation are used through the new proved general helper modules.
No module, declaration, or unit route is withdrawn. The quarantine archive is preserved;
the item is delivered with its Lean attachment intact.

## Where the brief, the DAG or earlier work was wrong

The item's node had empty proof/proof-dependency fields despite two nontrivial theorem holes;
this delivery records the actual argument. Finite direct-image exactness requires finite
presentation in the existing pro-etale theorem; the actual diagonal satisfies it because the
projective line is smooth over its base. No mathematical statement or definition correction
is needed. The normalization refactoring is definitionally equal to the original predicate.

The rework row referred to an import-closure build issue. Compilation uses the current source
and the compile service's private dependency overlay; the quarantined item is not withdrawn.

## New nodes

`lem-sp-diagonal-integral-unit-epi` states that for any closed immersion the canonical map
from the ambient constant integer sheaf to the closed direct image of the integer sheaf is
epic. This is the generator step, independent of coefficient towers and evaluation maps.
It is proved using the local ambient-open extension argument and the existing continuous
sheaf comparison. Sources: Milne, Section 9, p. 67, exact sequence (*) in Theorem 9.4's proof;
Bhatt--Scholze, Lemma 4.2.12. Empty schemes/charts and arbitrary bases are covered explicitly.

`lem-sp-closed-integral-hom-ext` proves extensionality on those pulled-back integer
generators for maps into any abelian sheaf. It combines the preceding epimorphism with the
sheafification universal property. It is a coefficient-independent uniqueness criterion,
strictly part of the supported quotient argument, and is proved without new holes.

`lem-sp-closed-tower-direct-image-exact` transports finite-level direct-image exactness
through the specified evaluation comparisons for any closed immersion locally of finite
presentation. It uses the existing finite pushforward theorem (Bhatt--Scholze, Lemma 6.1.17)
and the jointly faithful exact evaluation family. The item proves the finite-presentation
hypothesis for the actual diagonal and applies this helper. No hole is introduced.

Mathlib and blueprint searches for each helper found no exact existing statement; their
records include the queries and results. All existing public source declarations remain
unchanged. The definition refactoring and its consumer check are recorded in
`coord/changes/g7-finite-diagonal-normalization-sharing.md`.

`def-sp-single-boundary-normalization` defines the same finite boundary comparison after
forming degree-zero single complexes and the root map's shift in an arbitrary abelian
category. Its body is exactly an application of `finiteBoundaryEquality`; it adds no
hypothesis, equation, endpoint transport or choice. This moves repeated type checking
of specialized category witnesses into a generic construction. The supported normalization
unfolds to its original expression. The helper has no hole and is publicly imported by
the item because its definition uses it. Source: the same classes clauses (2)--(3).

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
