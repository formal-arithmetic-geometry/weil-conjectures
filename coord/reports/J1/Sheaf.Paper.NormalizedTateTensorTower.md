## What changed

Restored the assigned quarantined source and preserved its exact theorem statement,
public imports, definitions and Lean attachment. The theorem now assembles the
normalized derived reduction construction and the common single-degree local-model
result, then applies the proved zero tensor unit comparison. Added private proof
imports of NormalizedTateTensorTowerCore, NormalizedTateTensorTowerProperties and
NormalizedTateTensorTowerZero.

The two remaining geometric obligations are public theorems in separate new modules,
with sources, full proof plans, edge cases and matching DAG nodes. Neither is the
original result under another name: one constructs normalized reductions without
common models or constructibility; the other proves common models and constructibility
for an already given tower.

The zero tensor unit comparison is proved. Its private unitSquare lemma proves the
cancellation calculation for arbitrary functors and isomorphisms. Specializing this
lemma to the actual Tate unit maps proves finiteZeroIso_reduction. Naturality of
scalarComparison then transports the assumed normalization square to the required
e₀ square. This avoids repeatedly unfolding the large derived monoidal structures.

The item node now follows this implementation. No shared interface changed and no
consumer adaptation or change record is necessary. The unit's adic route is preserved.

## Proved and sorry left

Original hole closed: AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower.
Its proof from the named components is complete.

Additional proved declaration:
AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_zero,
node lem-pur-normalized-tate-tensor-unit. Its private unitSquare and
finiteZeroIso_reduction helpers also have complete proofs.

Holes added: two, each exactly the body of one named public theorem:

- AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_core,
  node lem-pur-normalized-tate-tensor-reductions, in
  Sheaf.Paper.NormalizedTateTensorTowerCore.
- AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_properties,
  node lem-pur-normalized-tate-tensor-models, in
  Sheaf.Paper.NormalizedTateTensorTowerProperties.

Actual holes: zero in the item; two in the delivery. This is a decomposition:
one upper hole closed and two lower holes added, net hole change +1.
It is not a sorry-free proof of the geometry below the item.

Validation: both geometric component statements compiled. The proved unit component
compiled in 40.8 seconds after replacing the large direct calculation by unitSquare;
profiling options were removed before the final compile. The direct calculation
previously exceeded 60 seconds, with kernel checking as its main cost. The generic
lemma reduced that cost; no limit was raised and no proof was replaced by a hole.
The final all-files compile and delivery preflight provide the final validation.

## No longer needed

No existing import, mathematical dependency, node or module is pruned. The original
geometric dependencies remain in the reduction and model component plans; the parent
now directly uses these components and the proved unit component.

The zero tensor clause needs no new sorried statement: it follows from the actual
scalar-unit formulas and the already required comparison square. No reconstruction
or exceptional-image theorem is imported to prove the assigned local tower result.

## Where the brief, the DAG or earlier work was wrong

The assigned source was initially absent from lean/ and preserved at the quarantine
path in coord/rework.tsv. It was restored into the sandbox. The shared source was
restored independently during the session and agrees with the archived source.
Absence was not treated as withdrawal, and no deletion is requested.

The original dependency declarations provide root lines and categorical operations,
but do not state the normalized strict-tower construction or its common-model
interface. Those two genuine parts of the argument are now explicit obligations.
The original theorem statement remains unchanged, including empty schemes, d=0,
arbitrary normalized root comparisons and equal quotient indices.

## New nodes

lem-pur-normalized-tate-tensor-reductions states the normalized strict derived
reduction component (original Steps 1--3), including existence of the finite
normalized root comparisons used by the zero tensor calculation.

lem-pur-normalized-tate-tensor-models states the common single-degree local-model
and finite constructibility component (original Step 4) for an already given
projection-normalized tower. Its bounds and actual scalar-linearity clauses are
exactly those needed by the original theorem.

lem-pur-normalized-tate-tensor-unit states the zero tensor unit compatibility for
an already given tower. It is proved from functor naturality and the explicit
unit comparison formulas, with no sorry and no geometric construction.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
