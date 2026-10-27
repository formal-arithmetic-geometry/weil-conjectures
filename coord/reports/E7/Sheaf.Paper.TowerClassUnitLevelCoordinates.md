## What changed

The item now constructs its finite unit isomorphisms from the actual constant-ring
adjunction and transports them through ordinaryPullEvaluation. The transpose
normalization is proved by cancellation of that evaluation isomorphism.

The new module Sheaf.Paper.TowerClassFiniteUnit proves exists_finiteUnitIso without
new holes. Its argument uses the regular module's global-section universal
property: pushforward along a final site functor preserves sections, so the
transpose of the unital coefficient map is invertible by the coyoneda criterion.
Pro-etale base change preserves terminal objects, hence is final. This directly
uses the actual project adjunction and avoids expanding the small-site tensor
construction or assuming a different pullback functor. Evaluation of the
coefficient system is identified with the regular module by its actual ring
identification; the comparison is identity on section carriers. The ring
adjunction inverse law gives the precise constant direct-image map.

Two unfinished parts are separated: exists_sectionGeometry chooses geometry with
identity underlying direct-image comparisons but asserts no unit maps;
unit_successor_compatibility asserts only the adjacent quotient square for
already supplied normalized maps, without existence or invertibility. The item
proves the passage from adjacent squares to all quotient transitions by applying
Mathlib NatTrans.ofOpSequence to the underlying section functors at each site
object. The adjacent module equations supply its naturality hypotheses; its
naturality at n <= m gives the required all-pair square.

Only the item, three new modules and their node records change. The original
signature and public import stay unchanged. The new imports in the item are
proof imports. All helper definitions construct their data explicitly; none
contains sorry. No existing shared definition, statement, instance, attribute,
public import or consumer is changed, and no change record is needed.

The original theorem signature was compared textually with the shared source
and is identical. All four modules compiled together. Profiling then identified
costly rewriting
through scalar restriction in the item. Explicit equality transport and local
irreducibility of comparison definitions reduced its single-file compile to
9.9 seconds. These attributes are local; no shared interface changes. The finite
unit theorem and all its private helpers compiled cleanly in 9.4 seconds after
local opacity refinements. Profiler settings are removed for delivery.

## Proved and sorry left

The hole in AlgebraicGeometry.ProEtale.SpTowerClasses.exists_unitLevelCoordinates
is closed by a complete proof from the two remaining construction/coherence
lemmas and the newly proved finite-unit theorem. The item has no remaining sorry.

Proved AlgebraicGeometry.ProEtale.SpTowerClasses.exists_finiteUnitIso
(node lem-sfb-tower-class-finite-unit), including invertibility and the exact
finite adjoint section formula. All private helpers are proved. The passage from
adjacent squares to every horizontal transition is also proved
from Mathlib NatTrans.ofOpSequence on underlying section functors.

Two holes are added, each the whole proof of a public named theorem:

- AlgebraicGeometry.ProEtale.SpTowerClasses.exists_sectionGeometry,
  node lem-sfb-tower-class-section-geometry-existence.
- AlgebraicGeometry.ProEtale.SpTowerClasses.unit_successor_compatibility,
  node lem-sfb-tower-class-unit-successor-compatibility.

This is a decomposition: one original hole closed, two strictly smaller holes
added. It is not a net hole-count proof gain. The finite unit construction is
finished; neither remaining statement repeats the original existential theorem.
The first has no coefficient-unit maps. The second supplies no maps and no
isomorphisms and covers adjacent indices only. The item constructs those maps,
proves their invertibility and normalization, and deduces non-adjacent coherence
from the supplied adjacent equations.

## No longer needed

No existing module, declaration or public import is removed or withdrawn; no
module is claimed globally pruned. Each new proof import is used.

The item's direct proof dependencies on
lem-sp-strict-system-geometric-realization,
lem-coef-ordinary-inverse-system,
lem-coef-ordinary-direct-system,
lem-coef-semilinear-ordinary-geometric-realization,
lem-coef-semilinear-geometric-derived-evaluation,
lem-coef-semilinear-geometric-tensor-localization, and
lem-coef-semilinear-derived-sections now belong below the two smaller unfinished
steps. They remain in the corresponding new nodes and are not globally
unnecessary. def-weil-pbc-proetale-operations supplies the actual finite
adjunction used by the proved finite-unit node. The successor calculation uses
the fields of def-coef-semilinear-geometry-base directly, rather than invoking
lem-coef-semilinear-derived-sections. That theorem remains a construction
dependency of the geometry node.

The detailed pullbackObjUnitToUnit plus scalar-extension-multiplication route is
unnecessary for the finite step: the same final-functor global-section argument
proves the result directly for the actual adjunction. In particular no small
model comparison or new tensor-multiplication lemma is imported for that proof.
The unit's statement and route stay intact.

## Where the brief, the DAG or earlier work was wrong

No mathematical counterexample or target-statement defect was found. The current
Geometry existence interfaces do not expose identity of levelPushUnderlying;
choosing an arbitrary existing Geometry does not justify that normalization.
The new geometry lemma isolates exactly this missing choice, independently of
all coefficient-unit comparisons.

The former proof plan treated all quotient squares as a single transposition
calculation. Only the adjacent square needs that calculation:
Mathlib NatTrans.ofOpSequence
extends these squares by ordinary sequence-site functoriality, including equal
indices. This reduces the remaining coherence statement.

The finite unit argument was shorter than the plan's explicit pullback/tensor
construction. It handles empty charts because it uses unital ring sheaf maps
and the universal property of module sections. The lowest index is the positive
coefficient quotient indexed by zero. No quotient flatness is assumed and no
coefficient quotient map is inverted. The naturality argument covers equal indices and zero modules as well.

## New nodes

lem-sfb-tower-class-finite-unit records the proved one-level isomorphism and its
exact section transpose, in Sheaf.Paper.TowerClassFiniteUnit.

lem-sfb-tower-class-section-geometry-existence records the normalized geometry
choice from the first step of the original node, in
Sheaf.Paper.TowerClassSectionGeometryExistence. It asserts neither finite unit
isomorphisms nor their horizontal compatibility.

lem-sfb-tower-class-unit-successor-compatibility records only the adjacent
horizontal calculation for supplied normalized finite maps, in
Sheaf.Paper.TowerClassUnitSuccessorCompatibility. The maps need not be
isomorphisms. The original item supplies the finite isomorphisms and derives
compatibility at arbitrary indices using NatTrans.ofOpSequence.

All three nodes retain the original source, chapter and unit. Their Lean
statements match their modules. The original node records the actual new route.
The searches found the finite unit/global-section API and adjunction naturality,
but no theorem supplying the normalized project geometry or its adjacent
quotient square. No change records are added.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
