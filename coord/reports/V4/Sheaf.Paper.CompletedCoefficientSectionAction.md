## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRealization_section_action`
by an actual scalar-normalization and free-generator argument. Existing signatures,
definitions, visibility, public imports and targets are unchanged.

The new proof first uses
`completedCoefficientRingComparison_existsUnique` and the specified completed-coefficient
inverse limit to identify the scalar isomorphism determined by `e.unitIso` with the underlying
inverse of the ring-sheaf comparison. It then reconstructs the section module of
`e.F` on a concrete free cell and applies automatic linearity into that free target.
Cancelling the underlying isomorphism proves the action identity on its distinguished
generator. Finally it applies `e.F` to the explicitly constructed generator-to-section
map and uses both internal linearity and naturality of `e.underlying.inv` to prove the
original identity for an arbitrary module and section.

Added `Sheaf.Paper.CompletedCoefficientFreeGenerator`. The free presheaf, its module
sheafification, the distinguished generator and the map to a specified section are
actual constructions using Mathlib's free-module, Yoneda and sheafification
adjunctions. `completedFreeDesc_generator` proves the required evaluation identity.
No data are chosen from an unproved theorem. The only postponed theorem is automatic
linearity of additive sheaf maps into these particular free targets; it does not
mention `CompletedRealization`, a functor, an equivalence or unit normalization.

The item's new imports are proof-private. A local proof that forgetting ring
structure preserves the inverse limit supplies the required joint monicity of
finite projections. No private declarations of the ring-comparison module are used.
The original node's proof and proof dependencies now follow this argument.

Validation: `lcompile.py --all` compiled both delivered modules successfully on
2026-10-27, with no errors or warnings. The generator constructions, evaluation,
scalar-normalization lemma and original theorem all have complete Lean proofs.
All profiling options were removed before this successful compile.

## Proved and sorry left

Original holes: one, in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRealization_section_action`.
Its proof body now has no holes, and the typed corollary still applies it unchanged.

New holes: one, exactly
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedFreeCell_automaticLinearity`,
in `Sheaf.Paper.CompletedCoefficientFreeGenerator`, attached to
`lem-sfb-diagonal-completed-free-generator`.

This delivery is a decomposition, not an axiom-free closure: one original hole is
closed by a complete combination proof and one strictly simpler obligation is added;
the net hole reduction is zero. The remaining obligation concerns only concrete free
targets and arbitrary additive maps. The scalar-normalization and generator-evaluation
parts are proved, as is the passage from free generators to arbitrary modules.

Edge cases checked in stating the new theorem: the empty scheme and empty test object,
zero sections and zero source, l=2, and sources with l-divisible sections. The source
module N is unrestricted; separatedness is required only of the constructed free
target. No Noetherian, finite-rank, finite-type or invertibility assumption was added.

## No longer needed

No original import was removed and no module is claimed pruned. The original direct
proof dependency `det-prop-sfb-qlbar-colimit-x-integral-limit` is now accessed through
the already proved normalized ring comparison rather than reproved here; its
mathematics remains transitively needed. The explicit parent dependencies are now
the normalized ring comparison, module sheafification and free-target automatic
linearity. There are no new scheme-morphism or direct-image obligations.

## Where the brief, the DAG or earlier work was wrong

The original plan's second step had no declared dependency for its non-elementary
local-free-module argument. Naturality alone does not supply its action identity on
free generators. The adopted source's automatic-linearity criterion handles a
separated target, but its existing finite-free specialization does not directly cover
the sheafified representables needed to reach arbitrary local sections. The new
obligation isolates that missing case instead of renaming the original arbitrary-
module realization identity. No existing statement was weakened or disputed.

## New nodes

`lem-sfb-diagonal-completed-free-generator` records automatic linearity of additive
maps into the module sheafification of an actual free representable, along a ring-sheaf
isomorphism. Its proof explains integer generation modulo l-powers, separation of
free targets using pro-etale repleteness, and the action-defect criterion. Its module
also contains the proved generator construction and evaluation needed by the parent.
No other existing module, node or change record is changed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
