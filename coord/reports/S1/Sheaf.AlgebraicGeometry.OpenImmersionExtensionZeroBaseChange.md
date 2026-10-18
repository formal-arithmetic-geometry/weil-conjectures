## What changed

Proved `AlgebraicGeometry.Etale.openImmersionExtensionZero_exact_baseChange` in
`Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`, preserving its exact
signature and visibility. The three exactness properties use existing instances.
The canonical mate is invertible by the existing general-coefficient theorem
`isIso_openImmersionLowerShriekBaseChangeMap`; its natural isomorphism lifts to
unbounded cochain complexes via Mathlib `NatIso.mapHomologicalComplex`.
Updated the node proof and proof dependencies to match this shorter route.
The unit `sk-rem-rest` has no realized statement or proof steps, so no unit route
is bypassed. Checked the source statements in Stacks 03S5 and 03S6.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.openImmersionExtensionZero_exact_baseChange`
(node `sbc-prop-extension-by-zero-and-arbitrary-base-change`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The unchanged theorem compiled through `lcompile.py` in 2.5 seconds before import
pruning; the final delivery checks compile the pruned version and inspect axioms.
The proof handles every open immersion and every base-change morphism, including
empty and identity open immersions, without additional hypotheses or boundedness.

## No longer needed

Removed the proof-only import
`WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules` and its direct
proof dependency `lem-weil-pbc-etale-shriek-base-change-modules`: the existing
open-immersion theorem works directly with `AddCommGrpCat`, so no integer-module
comparison is required. Removed that obsolete node from top-level `tool_uses`.
Its module and its further dependencies are unnecessary for this proof; no claim
is made that other consumers no longer need them. The exactness and extension-by-zero
nodes remain needed. No other existing direct proof dependency was pruned.
No geometric-stalk lemmas or separate complex lemmas were imported or introduced.

## Where the brief, the DAG or earlier work was wrong

The previous plan unnecessarily passed through constant-ring module sheaves for
the abelian-sheaf base-change assertion. The library already states the identical
canonical-mate isomorphism for arbitrary suitable abelian coefficients, including
`AddCommGrpCat`. Its node is `lem-cbc-extension-zero-base-change`.
The current blueprint proof repeats the invalid direct-image section formula
for extension by zero and contains the undefined expression `Z_V`; this was already
identified in the node's earlier split report. The delivery retains the unchanged
statement and uses the existing Stacks 03S6 proof by adjunction instead of that
section formula. Naturality and inverse identities on complexes are supplied by
Mathlib's existing degreewise natural-isomorphism construction.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
