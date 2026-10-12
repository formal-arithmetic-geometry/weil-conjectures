## What changed

Repaired the duplicate-theorem return. Removed all three copied private helpers
from `FiniteEtaleFiniteTypeClosedFibreStage`: `property_pullback_snd_iff`,
`property_pullback_snd_mono`, and `exists_finiteEtale_limit_stage`.
The item now imports `Sheaf.AlgebraicGeometry.FiniteEtaleAlgebraStage` and applies
its existing `AlgebraicGeometry.Scheme.exists_finiteEtale_limit_stage`.
Lean's `import all` makes the original private theorem available to this proof.
The defining module is unchanged and is not part of this delivery; no adapted
module, visibility change, or change record is needed.
No existing statement, definition, target signature, or public import changes.

The original reduction remains: obtain a cover-independent approximation cone,
apply finite-etale inverse-limit descent, transport the cover and pullback square
through the stage isomorphism, and construct the required isomorphism in `Over`.
The item's DAG now cites the existing algebra-stage node for its proved
inverse-limit helper rather than carrying a duplicated implementation.
The item compiled against the unchanged private source theorem using `import all`;
the final two-module sandbox is compiled and checked by the delivery dry run.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_finiteEtale_finiteType_closedFibre_stage`
(node `lem-weil-pbc-finite-etale-finite-type-closed-fibre-stage`).
No textual sorry remains in the item. The algebra-stage module is unchanged.

Added and still open:
`AlgebraicGeometry.Scheme.exists_proper_closedFibre_approximation`
(node `lem-weil-pbc-proper-closed-fibre-approximation`), in
`Sheaf.AlgebraicGeometry.ProperClosedFibreApproximation`.
This is one hole closed and one strictly simpler hole added, a decomposition
with zero net holes closed. The approximation has no cover input, cover output,
or descent assertion. Existing imported holes are unchanged.
The reuse repair adds no holes and proves no previously open helper.

Edge cases of the approximation remain as previously checked: I = top gives empty
closed fibres; I = bottom gives the underlying approximation; the zero ring is
allowed. An empty cover needs no exception, and the directed index is nonempty.

## No longer needed

Removed the copied declarations `property_pullback_snd_iff`,
`property_pullback_snd_mono`, and `exists_finiteEtale_limit_stage` from the item.
Their original implementations remain in `FiniteEtaleAlgebraStage`.
Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.DescendFinite`,
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`;
the reused helper retains them in its defining module.

The earlier reduction removed direct item imports
`Sheaf.AlgebraicGeometry.LimitAffineTransition` and
`Sheaf.AlgebraicGeometry.ProperLimitNoetherian`; both remain imported by the
approximation module. No globally pruned node or module is claimed.

Old direct dependencies now supplied through the reused algebra-stage helper:
`def-sbc-locally-finite-presentation`, `def-weil-etale-morphism`,
`def-weil-finite-integral-morphism`, `lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-descend-etale`, `lem-weil-pbc-descend-finite`,
`lem-weil-pbc-qcqs-morphism-permanence`, and `thm-pd-spreading-out`.
Old direct dependencies retained by the approximation node:
`def-weil-proper-morphism`, `lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-proper-base-change`,
`lem-weil-pbc-proper-limit-noetherian`, `lem-weil-pbc-spec-colimit-limit`, and
`pqf-def-affine-morphism`. These are moved dependencies, not global pruning.
No realized statement or step of `sk-thm-p1` is bypassed.

## Second reading by W3

1. Compared the delivered stage module with the repository version. The theorem
   signature and all existing declarations are unchanged; only the proof and its
   proof-only imports differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. They compile cleanly;
   the only remaining `sorry` is the named approximation theorem, and no forbidden
   declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the proof against the existing finite-etale inverse-limit helper and the
   approximation statement. The proof uses the helper exactly at its stated cone,
   transports the pullback square through the stage isomorphism, and preserves both
   projection equalities. Verdict: pass.
4. Checked pruning and DAG synchronization. The copied private helpers and their
   direct imports were removed; the item's node records the two actual proof
   dependencies, while the approximation node records its own open dependencies.
   Verdict: pass.
5. Checked the unit route and statement strength. The approximation remains an
   independent first step and the finite-etale descent helper remains the descent
   step; no target or unit statement was weakened or bypassed. Verdict: pass.

Changed during second reading: added this review record; no Lean proof changes were
needed after compilation.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied private theorems because they were inaccessible from
another module. The landing check correctly rejected those duplicate statements.
The repair imports and reuses the existing private general helper with `import all`;
there is no renamed duplicate and neither property helper is re-proved in the item.
The stale second-reading section from the returned version has been removed so the
second reader can review the repaired files independently.

The original spreading-out node records a morphism-descent declaration, whereas
object descent uses `Scheme.exists_isPullback_of_finitePresentation` in the same
source module. That application is now solely in the reused existing helper.
The earlier searches found no exact closed-fibre approximation theorem;
LeanSearch's Internal Server Error was recorded as unavailable, not a negative result.

## New nodes

`lem-weil-pbc-proper-closed-fibre-approximation` isolates the inverse system,
proper finite-type models, and projection equations. Its source is Tag 0GS2,
General case, first approximation paragraph, and proper approximation Tag 0A0P.
Its docstring gives the quotient colimit argument, commuting limits, affine
transitions and qcqs of proper closed fibres. Its proof remains open independently
of cover descent. No additional node is introduced by this repair.
No existing source declaration or interface is changed, so no change record is needed.
