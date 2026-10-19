## What changed

Proved twelve of the thirteen original holes in
`lean/Sheaf/Paper/KoszulReconstruction.lean`. The principal theorem's original hole
is retained, with its existing source, proof in words and DAG node. No obligation
has been renamed or moved, and no new hole is introduced.

The supporting constructions now include Grothendieckness of strict towers,
additivity of limit, normalized quotient and ordinary-limit units, descent and
uniqueness of the derived completion unit through the K-flat localization, the
Koszul product/fibre functor laws, quasi-isomorphism invariance of that functor,
naturality of its unit, and its unit-compatible intrinsic comparison.

Added `lean/Sheaf/Paper/CompletedAdicKoszulKFlat.lean`, with a complete proof that
the recorded completed exterior Koszul complexes are K-flat. An exterior-power
basis presents each constant term as a finite sum of units. Exact finite sums and
the bounded-above flat criterion give K-flatness before changing coefficients;
the existing change-of-rings theorem and the scalar-extension witness's actual
object and morphism equations give the result over the completed coefficient
sheaf. This includes empty generator lists, zero rings, and exterior degrees
above the rank. No regularity assumption is added.

The fibre proof uses this K-flatness, the existing K-flat tensor transport theorem,
and exact countable pro-etale products. Homology's product comparison proves the
product map is a quasi-isomorphism. A proved identification of the two cone-map
APIs and the distinguished-triangle argument give the fibre result.

Refactored the unclaimed module `Sheaf.Paper.CompletedAdicCoefficientDatum` by
bundling its same chosen derived reduction pair in `DerivedReductionModelData`.
Generic counit and normalized-unit definitions retain all localization factors.
The bodies of `completedAdicReduction`, `reconstructionReductionCounit`,
`reconstructionReductionComplexCounit` and `reconstructionUnitOnKFlat` are
reexpressed using this API. The original and new terms are definitionally equal;
all existing public signatures, visibility, mathematical definitions and target
statements stay the same. This is a performance repair: profiling the earlier
specialized completion-unit proof measured 30.9 seconds of kernel checking for
that theorem alone. The generic API removes that repeated concrete conversion.
The completed twelve-proof module compiled through `lcompile.py` in 38.7 seconds
and again in 50.4 seconds. Its unchanged direct downstream consumer
`Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones` compiled against this packet
in 8.0 seconds. Four separate `rfl` checks verified the old/new definition bodies
are definitionally equal; those checks compiled in 23.2 seconds. Diagnostic
modules and the unchanged consumer copy are excluded from the delivery.

The definition changes and direct-consumer checks are recorded in:

- `coord/changes/M6-completedAdicReduction.md`
- `coord/changes/M6-reconstructionReductionCounit.md`
- `coord/changes/M6-reconstructionReductionComplexCounit.md`
- `coord/changes/M6-reconstructionUnitOnKFlat.md`

## Proved and sorry left

Closed 12 of the original 13 holes; added 0 holes; split off 0 obligations.
All twelve closed declarations are in namespace `AlgebraicGeometry.Scheme`:

- `reconstructionTowers_grothendieck`
- `reconstructionLimit_additive`
- `reconstructionQuotientUnit_exists`
- `reconstructionOrdinaryUnit_exists`
- `reconstructionTowerCounit_isIso`
- `reconstructionCompletionUnit_exists`
- `reconstructionKoszulProductMap_comm`
- `reconstructionKoszulFiberMap_id`
- `reconstructionKoszulFiberMap_comp`
- `reconstructionKoszulFiberFunctor_inverts`
- `reconstructionKoszulUnit_naturality`
- `reconstructionKoszulIntrinsicComparison`

The item's actual remaining hole count is 1:
`AlgebraicGeometry.Scheme.koszulReconstruction`, attached to
`prop-weil-pbc-koszul-reconstruction`.

The new theorem `AlgebraicGeometry.Scheme.completedAdicKoszul_isKFlat` is fully
proved, with zero holes, and has its own node. All private helpers are proved.
The adapted coefficient module retains its nine original, unchanged holes:
`completedAdicRing_mul_comm`, `completedAdicFiniteModuleStep_exists`,
`completedAdicOrdinaryTower_additive`, `completedAdicReduction_exists`,
`completedAdicFiniteRing_mul_comm`, `completedAdicRestriction_exact`,
`completedAdicFiniteReduction_comparison`, `completedAdicBalance_exists`, and
`completedAdicCommProjection_comp`. All are in namespace
`AlgebraicGeometry.Scheme` and attached to
`def-weil-pbc-adic-coefficient-datum`; none is a hole added by this delivery.

## No longer needed

Removed the unused proof imports `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescent`, `Sheaf.Paper.AdicCoefficientDatum`,
`Sheaf.Paper.CompletedConstantSheafReduction`, and
`Sheaf.Paper.ConstantCompletionEquivalence`. The first two are replaced for the
proved supporting constructions by the universe-independent Grothendieck, K-flat
and direct cone/localization APIs. The last two remain part of the principal
comparison's outstanding proof plan; their absence as unused proof imports is
not a claim that their mathematics has been pruned. Their node dependencies are
retained. No module or DAG node is withdrawn.

The intrinsic comparison needs only the localization factorization and the
already recorded intrinsic model; no additional comparison lemma is imported.
The K-flat proof uses the existing bounded-flat and change-of-rings criteria;
no separate presheaf/sheaf adjunction generalization is delivered. Those
experiments remain only in the scratchpad.

## Where the brief, the DAG or earlier work was wrong

The retained report was stale: it listed ten closed holes and an unvalidated
completion-unit draft. Both the completion-unit descent and the fibre-invariance
argument now have checked proofs. The initial continuation dry run failed at the
unvalidated draft; no interrupted delivery was pushed.

The stated generic comparison `ConstantCompletion.koszul_quotient_reflector`
does not directly instantiate to the principal theorem. Its site is a
`SmallCategory` in the coefficient universe; it uses its own completed constant
ring, a tensor/dual Koszul presentation, its chosen derived quotient pair and its
own right-derived limit. This item uses the actual finite-coefficient sheaf
limit on the pro-etale site and the recorded exterior Koszul model. The required
bridges include site/size transport, finite quotient identifications, the
exterior-to-dual-tensor Koszul comparison, and compatibility of the independently
normalized units. Related existing constant-coefficient comparison declarations
also live in a different coefficient category. These are interface and model
comparisons still needed for the retained principal hole, rather than a reason
that holed dependencies cannot be used. No statement is disputed or weakened.

Importing exact countable pro-etale products also exposes generic integral
coefficient instances. Fixing their coefficient universes locally avoids stuck
universe maxima during elaboration. These local instance attributes do not
change the global instance search seen by consumers.

No shared-repository file, launcher script, compiler limit, budget metadata or
target statement was edited. No forced adaptation of another group's module
was necessary.

## New nodes

`lem-weil-pbc-completed-adic-koszul-kflat` records the fully proved K-flatness
result in `Sheaf.Paper.CompletedAdicKoszulKFlat`. Its proof uses the exterior basis,
exact finite sums, the existing independent-universe bounded-flat criterion and
the existing change-of-rings criterion. Its three Mathlib searches and source
references are recorded in the node. It introduces no remaining work item.
`def-weil-pbc-derived-reduction-model-data` records the generic reduction API in
the adapted coefficient module. All its properties are proved; it adds no hole.
The older datum node's primary attachment belongs to a different module, so that
attachment is retained unchanged. The reconstruction node records the twelve
supporting proofs while retaining its principal comparison plan. The four change-record paths
are listed under `What changed` above.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
