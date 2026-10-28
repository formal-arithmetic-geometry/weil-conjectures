## What changed

Corrected and proved `AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_comparison`
in `Sheaf.Paper.LisseFiniteLevelEtaleModelComparison`. The old statement tried to
identify an arbitrary supplied etale complex D with an unrelated actual pullback.
The replacement descends a specified bounded proetale complex K whose cohomology has
finite locally constant etale models. It constructs D by derived direct image and
uses the classical derived counit for the comparison, reflects cohomological bounds,
and lifts cohomology isomorphisms by full faithfulness. The two private helpers bridge
the small and standard derived cohomology models and transport classicality across
an isomorphism. All four private proof imports are used; the public import is preserved.

Adapted `Sheaf.Paper.LisseFiniteLevelEtaleModel` (unclaimed when checked against the
current claims). Its theorem signature and public imports are identical. Define K
as the inverse fixed realization of the actual pullback, obtain its bounded lisse
cohomology, obtain etale cohomology models from `proEtale_lisse_origin`, and apply the
corrected comparison. Apply fixed realization to the resulting isomorphism and compose
with its actual equivalence counit. No arbitrary etale model or witness chosen from
an unproved existence theorem supplies object data. The actual derived inverse and
right adjoint determine both constructed objects up to the isomorphisms used.

Added `Sheaf.Paper.LisseFiniteLevelInverseCohomology` for the remaining local scalar
cohomology calculation. Updated both existing nodes' proof routes and added the
cohomology node. No target signature, public definition, or adopted source module changes.

Validation: the corrected comparison, new cohomology statement, and adapted parent
compiled together in import order (6.6 s, 3.5 s, and 5.0 s). The unchanged direct importer
`Sheaf.Paper.LisseFiniteLevelEtaleDescent` also compiled against this overlay (4.5 s).
Its temporary unchanged source copy was removed from the packet after the check. The delivery tool performs the final compilation, consumer, and axiom checks.

## Proved and sorry left

The corrected `AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_comparison`
is completely proved, with zero sorry. Both private helpers are proved. The unchanged
statement `AlgebraicGeometry.Scheme.lisse_finite_level_etale_model` has a complete Lean
proof from the named cohomology lemma and the existing classical comparison declarations.

The old arbitrary-D statement was false and is not counted as a proved original hole.
Its sorry is retired by an explicit statement correction, with the parent statement
preserved. This packet is a statement repair and a decomposition, not a net hole closure:
one original hole removed, one strictly smaller cohomology hole added, net zero.

Exactly one sorry remains in the packet:
`AlgebraicGeometry.Scheme.lisse_finite_level_inverse_realization_cohomology`, in
`Sheaf.Paper.LisseFiniteLevelInverseCohomology`, node
`new-lem-weil-pbc-lisse-inverse-realization-cohomology`.
Its conclusion concerns only boundedness and locally constant finite cohomology of
an explicitly constructed proetale object. It asserts neither existence of an etale
derived complex nor a derived comparison isomorphism. Those subsequent steps are now
proved in the item and parent; the new theorem is a genuine earlier step of the argument.

## No longer needed

The parent no longer imports `Sheaf.Paper.LisseFiniteLevelEtaleModelProperties`, and
its route no longer uses `new-lem-weil-pbc-lisse-finite-level-etale-model-data`.
That helper chose D=0 without tying it to the actual pullback. Its existing theorem
and module are preserved; no declaration or file is withdrawn.

The comparison no longer needs `lem-weil-pbc-comparison-pullback` or
`lem-weil-pbc-comparison-finite-local-constancy-reflection` as direct proof dependencies.
The generic derived counit replaces the proposed gluing of arbitrary models, and full
faithfulness lifts each supplied finite-lisse cohomology model directly. These lemmas
may still have other users and are not withdrawn globally. The comparison no longer
uses `lem-sf-proetale-locally-constant-origin` directly: the parent now applies it to
the actual K before invoking comparison, so it remains needed in the repaired route.
Finite scalar, adic tower and normalization nodes have been removed from the comparison's
statement dependencies because its corrected statement is independent of those data;
the parent and new cohomology calculation retain the applicable scalar dependencies.

No unit statement or realized proof step of `sk-thm-properbasechange` is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (resolved by this packet): the original comparison quantified over
D without relating D to the local models. Take a nonempty base with nonzero finite
coefficients, E=N=0 and nonzero bounded constant D. Every old hypothesis holds, but the
claimed realization isomorphism to zero does not. Conversely the parent selected D=0,
which cannot model a nonzero actual pullback. The preceding worker's dispute was valid.
The one-step DAG plan to glue those unrelated data therefore could not prove its claim.

The corrected statement follows Stacks Project `proetale.tex`,
`lemma-compare-derived` (Tag 09B1) and `lemma-compare-locally-constant-derived` (Tag 099Z).
It specifies K first and constructs its model by the invertible derived counit.
The only DAG citer is `new-lem-weil-pbc-lisse-finite-level-etale-model`: its unchanged
conclusion holds via the adapted proof in this packet. Its dependency route is updated.
The statement-change record includes this citer, the old statement and old dependency
and proof fields. The change record records the verbatim old and new Lean signatures.

Searches of Mathlib, the adopted source and `Sheaf` found no direct scalar inverse
cohomology theorem. The existing private bounded-constructible origin argument adds
Noetherian/constructibility hypotheses absent here; the condensed local-cohomology
argument has different coefficient and compactness hypotheses. Instead, the corrected
proof directly uses the already proved classical sheaf and classical derived equivalences.
The new cohomology statement was checked on empty schemes, zero coefficients, zero E,
and arbitrary covering sieves: covering-local detection of zero and finite-model
local constancy handle these cases, without compatibility of chosen local markings.

## New nodes

`new-lem-weil-pbc-lisse-inverse-realization-cohomology` states the bounded lisse
cohomology calculation for the explicitly constructed inverse finite scalar realization.
Its source is the local constant model calculation of Stacks Tag 099Y with exact inverse
image and constant sheaves (Tags 03DC and 093J), and the project's explicit finite scalar
equivalence. Its three proof steps specify scalar transport of the actual derived local
models, covering-local cohomological zero detection, and finite-model local constancy
and finite geometric stalks. Existing declarations for each of the latter operations
are cited by their DAG nodes. LeanSearch, LeanFinder and grep queries are recorded;
none gives an exact duplicate. The node remains in the existing proper-base-change unit
and records the inherited blueprint ancestry.

Change record: `coord/changes/N1-lisse-finite-level-model-comparison-repair.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelEtaleModel": "a1ec5c15ad67ec3e0a91e4e8b0b69910260c9388", "Sheaf.Paper.LisseFiniteLevelEtaleModelComparison": "018b0825150d1173ba99ee96c24100c8fcca8d9f", "Sheaf.Paper.LisseFiniteLevelInverseCohomology": "b229929d6e943fba8658b314b4befc650d7b1ac1"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleDescent": {"hash": "bdcdcb3186f0e12e37a1aae23babc13c1f097fcf", "status": "OK"}}, "seconds": 18, "time": "2026-10-28T10:26:10+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
