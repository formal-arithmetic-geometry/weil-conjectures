## What changed

Proved `AlgebraicGeometry.exists_common_degree_twist_ample` in the item module using the
existing common-degree invertibility and homogeneous-section basis theorems. Private proved
helpers construct the finite homogeneous cover, transfer affine nonvanishing sections through
the multiplication isomorphisms, and transport the result along `j.isoOpensRange`.
The multiplication formula is checked on all local pure tensors, including exponent zero in
the inductive helper. Existing public statements and definitions are unchanged.

Added private proof imports of the existing ampleness isomorphism and positive tensor-power
results, nonvanishing under restriction, tensor-power restriction comparisons, and affine
morphism facts. Updated the item's DAG proof to record those steps and dependencies.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_common_degree_twist_ample`
(node `lem-trf-proj-qc-open-twist-ample`), the item's one original hole.
Added: none. Remaining holes in delivered modules: none. All private helpers are proved.
Final single-file compile passed cleanly in 22.2 seconds.
The two existing Proj lemmas `AlgebraicGeometry.Proj.commonDegreeTwistInvertible` and
`AlgebraicGeometry.Proj.twistSectionBasicOpen` remain proof dependencies; their existing
holes are not changed by this delivery. This closes one hole from the stated dependencies,
with zero holes added or split off.

## No longer needed

No original dependency or import is withdrawn. No modules or nodes are pruned.
The finite cover construction handles the empty open by an empty cover and product one,
so no separate empty-scheme lemma is needed. Positive tensor powers use the existing
`isAmple_positive_tensorPow`, avoiding a second homogeneous-section powering argument.

## Where the brief, the DAG or earlier work was wrong

The original plan described the mathematics correctly but omitted the Lean transfer from a
literal open inclusion to the arbitrary open immersion in the statement. The private helpers
prove that transfer explicitly. The literal-open proof uses the affine-basis clause, not the
false inference that every intersection of the given open with a standard affine open is
affine. The unit route is preserved; no unit statement or realized step is bypassed.

The existing off-unit results `lem-sc-ample-iso`, `lem-sc-ample-positive-tensor-power`,
`lem-sc-nonvanishing-locus-restrict`, and the restriction comparison definitions/theorem are
used as tools for section transport; the local Proj route does not duplicate those general
facts. All are already proved in the source library.

The interrupted run left an unconfirmed compile and a completed draft report. On resumption,
the latest compile was rerun and the restriction-section conversions were repaired. Explicit
`restrictAppIso` applications avoid expensive inference through the scalar structures of
successive restrictions; the file compiles without raising any heartbeat or wall-time limit.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
