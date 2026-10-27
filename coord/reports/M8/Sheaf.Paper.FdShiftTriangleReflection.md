## What changed

Proved `WeilConjectures.fdShiftTriangleReflection` in
`lean/Sheaf/Paper/FdShiftTriangleReflection.lean`, keeping its full signature and every
existing definition unchanged. Added proved private helpers for literal restriction,
normalized shift components, finite inverse triangles, triangle comparison components,
and exact descent. Reused the generic pair-shift construction
from `Sheaf.Paper.SfFrameworkCommonStageDescent` through a proof-only `import all`.
The companion `fdCommonStageConeIdentification` and its existing proof are retained.
The generic private reflection lemma is fully proved here; it abstracts the categories
and their finite-model criteria, then specializes to the two actual coefficient systems.

The finite inverse is `(J.Φ M).inv`, with the equivalence adjunction and its induced shift.
The comparison is assembled from the finite counit and the stage inclusion comparison.
The Hom bijections supply Full and Faithful; Mathlib lifts the triangle isomorphism and
proves its required image equation. A compatible right adjoint is exact directly.
The item's DAG proof and proof dependencies have been updated to this implementation.

Validation: remote single-file compilation passed in 41.9 seconds. Profiling options
were removed for delivery; the delivery tool performs the final compilation and preflight.
Local irreducibility of the pair functor and stage inclusion inside the descent proof
avoids repeated expansion of their quotient constructions; proved generic formulas
supply their required components. The original companion proof remains unchanged.

## Proved and sorry left

Closed: `WeilConjectures.fdShiftTriangleReflection`
(`lem-fd-shift-triangle-reflection`), the only original hole. Added: none.
Remaining textual holes in the item: none. The proof uses the existing named dependency
statements, including the published common-stage triangulation and framework shift
normalization; it does not claim to close those modules' independent holes.

## No longer needed

No existing public imports or declarations are removed, and no modules are withdrawn.
There are no new public intermediate statements or split-off holes. Mathlib's fully faithful
`mapTriangle` and `Functor.map_distinguished_iff` replace the bespoke component lifting
argument of original step 6. `Adjunction.isTriangulated_rightAdjoint` replaces the
essential-surjectivity/global-equivalence construction of original step 7. The finite
model, its specified counit components, and the companion cone formula remain proved.
All original declared dependencies remain used by the statements or proofs.

The already proved generic helpers of `lem-sf-framework-common-stage-descent` are used
as tools for shift descent, not its framework-to-framework theorem as a replacement for
the mixed source/target assertion. `thm-weil-pbc-verdier-axioms` supplies exact target
inclusions and the finite-model distinguished-set criterion for the actual PBC system.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The assumptions involving the finite-field datum,
linearity, and unit normalization are stronger than the proof needs, but remain verbatim.
The latest blueprint moved `def-fd-trace-function` to `sk-cor-plancherel`; it no longer
contains the old final coefficient-comparison sentence. This delivery proves the assigned
existing node and Lean statement; it does not change the unit or chapter route.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
