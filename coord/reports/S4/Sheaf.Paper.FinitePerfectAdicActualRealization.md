## What changed

Corrected `finitePerfectAdic_actual_realization`: choose the etale levels L together
with their realization, instead of asserting the result for arbitrary stalkwise
models L. The structure `FinitePerfectAdicActualRealizationData` is unchanged.
Adapted the sole caller, `FinitePerfectAdicActualNormalization`, to obtain L and
its realization together; that module's theorem signature and structures are unchanged.
The change record is `coord/changes/S4-finite-perfect-actual-descent.md`.

Constructed the scalar realization explicitly in `FinitePerfectAdicScalarRealization`:
restriction from U to W, transport to the slice, associated module sheafification
along the locally bijective finite-scalar unit, restriction of the completed action,
and termwise derived localization. Proved local bijectivity, the associated-sheaf
equivalence, cancellation of weak etaleness, and exactness of the composite.

Separated the associated-sheaf scalar compositor, the comparison with constant
algebraic models, and descent of the actual quotients retaining their comparison.
The latter two parts use the same fixed realization and proved scalar compositor, so their
normalized squares assemble by field construction, without an arbitrary choice of
functor or a simultaneous marking. Every new postponed theorem has a complete
proof in words, a source, a node, and its own module.

## Proved and sorry left

The delivery decomposes the repaired obligation into two strictly smaller steps.
The item originally had one hole, `AlgebraicGeometry.Scheme.finitePerfectAdic_actual_realization`.
Its old statement is false and is repaired here; this is not reported as a proof of
that old statement. The repaired existence theorem is fully proved from the named
component statements, and the item has zero remaining holes. This is a statement
repair and decomposition, not a net proof of the original hole.

New holes (two):
- `AlgebraicGeometry.Scheme.finitePerfectAdicScalar_model`,
  node `lem-weil-pbc-finite-perfect-adic-scalar-model`.
- `AlgebraicGeometry.Scheme.finitePerfectAdic_actual_level_descent`,
  node `lem-weil-pbc-finite-perfect-adic-actual-level-descent`.

The scalar realization and its local-bijectivity, equivalence and exactness lemmas
are proved. Also proved `finitePerfectAdicAssociated_coherence_existsUnique`: the
explicit map extended from the abelian sheafification unit is natural and invertible,
and fixes the ordinary compositor uniquely. The consecutive scalar-unit square,
composition of ordinary restrictions and derived scalar compositor are all proved.
The compositor is therefore built from proved data, with no additional hole.
All six delivered Lean modules compile in import order; the sole direct importer
`FinitePerfectAdicActualNormalization` also compiles against the repaired theorem.
Every file is below the 60-second limit.
No new axiom, hollow definition, or source-library alteration is introduced.

## No longer needed

Removed the parent's private import of `Sheaf.Paper.FinitePerfectAdicActualLevels`
and its application of `finitePerfectAdic_actual_levels`: choosing arbitrary level
data separately discards the very comparison the realization argument needs.
The existing module is still imported for `FinitePerfectAdicActualLevelData`, so it
is not withdrawn and its hole is not counted as pruned.

The item's former direct proof dependencies on completed constant reduction,
ringed derived restriction, and ringed tensor pullback are replaced by the explicit
realization and its separate comparison steps. These generic results remain needed:
completed constant reduction by the model-comparison step; ringed restriction by the
tower definitions; tensor pullback by the actual descent normalization step.
The new model-comparison module imports `FinitePerfectAdicConstantCohomology`
directly; it does not import the unused constant universal-normalization theorem.
No existing module or declaration is deleted; no module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old theorem is false because M is phantom in `FinitePerfectAdicActualLevelData`.
Bounded lisse cohomology, inhabited Isom stalks with constant T and universal arrows
do not identify L with the actual quotient tower. For X = Spec(R), V = X, A = F3,
I = 0 and rank-one constant T, let M be the sign local system for Gal(C/R), and L
the constant etale tower. All the hypotheses and level-data fields hold, with
markings on Spec(C). Since the actual and model inputs to realization coincide,
the old conclusion identifies the sign local system globally with the constant one.
Stacks 09C6 instead explicitly chooses descended levels with K_n = epsilon inverse L_n.
The repaired theorem records that existence and preserves the complete parent goal.
The statement_change audits its sole DAG citer and the change record lists both Lean
users. No target or unit route is changed.

The inherited item blueprint.from incorrectly referred to a split node which is not
a blueprint node. It is reported here for maintenance; the inherited field is preserved in this stage-3 packet.
Searches of the current blueprint and library found no duplicate of the explicit
scalar realization or its complete normalized comparisons. Existing generic scalar
restriction and sheafification APIs are used. The input has already been split many
times; the ordinary scalar square is now proved. The two remaining obligations
are separate mathematical parts: the constant model alone and actual descent alone. None
restates the complete realization package under another name.

Edge cases were checked mathematically: n = 0 still means exponent one; zero rings
and empty slices use the same sheafification and restriction functors; bounded
perfect complexes include the zero complex; separate markings never imply a global
marking. No nonempty site or nonzero ring is assumed.

## New nodes

`def-weil-pbc-finite-perfect-adic-scalar-realization`: the explicit ordinary and
derived realization, with proved equivalence and exactness; contains no hole.

`lem-weil-pbc-finite-perfect-adic-scalar-coherence`: the uniquely normalized ordinary
associated-sheaf scalar square, its application to quotient presentations and the
derived compositor, all proved. This has no M, T, descent object or model comparison.

`lem-weil-pbc-finite-perfect-adic-scalar-model`: only the constant algebraic model
comparison and its arrow square, with no actual quotient or descended L.

`lem-weil-pbc-finite-perfect-adic-actual-level-descent`: choose the etale descent of
actual quotients retaining its comparison and normalization; no constant-model
comparison or unspecified realization functor is included.

Change record: `coord/changes/S4-finite-perfect-actual-descent.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicActualLevelDescent": "9643b00c445e893408a26c8d082607860c3467b5", "Sheaf.Paper.FinitePerfectAdicActualNormalization": "6054f187766b4db38c4be4a59c52839207a440d1", "Sheaf.Paper.FinitePerfectAdicActualRealization": "d28db9d0430e4f542d0cf1d54be4806b63bf1d90", "Sheaf.Paper.FinitePerfectAdicScalarCoherence": "92503fce5929c2e9f888de175efbf509e9f760ee", "Sheaf.Paper.FinitePerfectAdicScalarModel": "cdf5e417164dcd87b059e983569b322673ed0717", "Sheaf.Paper.FinitePerfectAdicScalarRealization": "aeaaf812057751da49794ca0914ecce428faf123"}, "results": {"Sheaf.Paper.FinitePerfectAdicIsomorphismPresentation": {"hash": "6fbf1f28b1faaf41050ba1959103a0fd803a8197", "status": "OK"}}, "seconds": 24, "time": "2026-10-28T04:31:39+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
