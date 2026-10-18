## What changed

Proved `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence` from Mathlib's generic
`Adjunction.leftAdjointCompIso_id_comp`, `leftAdjointCompIso_comp_id`, and
`leftAdjointCompIso_assoc`, together with the existing `Etale.upperStarComp` coherence laws.
Added the proof-only import `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCompCanonical`.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence` is proved,
including both identity laws and three-fold associativity. One lower theorem remains sorry:
`AlgebraicGeometry.Etale.openImmersionLowerShriekComp_canonical`, node
`lem-cbc-extension-zero-composition-canonical-comparison`; it identifies the canonical comparison
with the generic left-adjoint comparison and handles dependent identity/associativity transports.

## No longer needed

The proof uses every original dependency needed by the generic adjunction route. No original
proof-dependency node or import was pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omitted the dependent transport needed to identify the mate-defined
comparison with `leftAdjointCompIso`; this is recorded as the lower split node above. The target
route itself is correct and reduces directly to Mathlib's generic coherence lemmas.

## New nodes

`lem-cbc-extension-zero-composition-canonical-comparison` is stated in
`lean/Sheaf/AlgebraicGeometry/Etale/OpenImmersionLowerShriekCompCanonical.lean` and records the
canonical-mate identification used by the target proof.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
