## What changed

Reduced `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinement`
to the coefficient-restriction and arithmetic-selection squares for the actual
normalized `compositionC`. The new module
`Sheaf.Paper.StrictRefinementRestrictionSquares` states those two faces together
as one named theorem. It uses neither native reduction/support towers nor
constructible origins, inverse refinement isomorphisms, or derived limits.

The parent proves inverse-mate naturality from scalar adjunction units, obtains
the scalar comparison square using `comparison_pasted`, pastes with naturality
of `reductionBalancing`, and cancels the prescribed `supportModel` maps. It then
inverts the two normalized refinement comparisons and derives the total-limit
square by naturality of `scalarLimitTensor` and `scalarLimitRestriction`.
Private component formulas expose the existing support-refinement and scalar-arrow
maps without expanding their native functors in the transport proof. A generic
transport lemma takes those component formulas as hypotheses. Structural type
congruence, following the existing `SmoothTensorCompositionEquation` method,
normalizes functor-composition presentations and proof-irrelevant instances both
at theorem arguments and at the assembled equality.
Every resulting equality and assembled proof is checked by Lean's kernel.
Local irreducibility and synchronous elaboration control proof-checking cost.
All existing public statements and constructions are unchanged.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinement`.
This is a decomposition, not a net hole reduction: one original hole is replaced
by one lower theorem hole, with the assembly proved completely in Lean.
The original module started with four holes and now has three.

Original holes retained, all attached to
`lem-pur-compact-support-strict-scalar-refinement`:

- `WeilConjectures.PurStrictScalar.scalar_clopen_projection`.
- `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`.
- `WeilConjectures.PurStrictScalar.scalar_compactification_composition`.

Added hole:
`WeilConjectures.PurStrictScalar.strictRefinementRestrictionSquares`, node
`lem-pur-strict-refinement-restriction-squares`.
Its two clauses concern restriction of the normalized constant-coefficient
refinement, a strict part of Step 7. The parent separately proves the mate
calculation, reduction balancing, native-model transport, inversion, and limit
naturality. No holes occur in the new private helpers or in definitions.

Validation: both modules compiled remotely with all proof and kernel checks enabled.
The final packet removes profiling options and diagnostic heartbeat caps; the clean
compile and delivery preflight are recorded by the delivery tool. All 14 existing
public signatures remain verbatim; only the named restriction theorem adds a hole.

## No longer needed

No existing import, module or node is withdrawn. The direct parent proof edges to
`def-weil-derived-complete-integral-detailed` and
`lem-sf-proetale-constructible-origin` are replaced by the existing E/F origin
lemmas, which encapsulate that input; this does not withdraw their modules.
The earlier clopen, proper/open scalar and composition assertions remain public,
and their existing proof dependencies remain needed. In particular zero Lean
importers would not justify withdrawing a dependency of an unfinished parent.
The new restriction lemma supplies the two previously unstated faces of the
refinement assembly; it does not change the unit route.

## Where the brief, the DAG or earlier work was wrong

The existing Step 7 prose did not expose coefficient restriction and arithmetic
selection as usable equations for `compositionC`. The new theorem records those
faces before taking scalar mates. Step 7 of the node now records exactly this
reduction and the complete Lean assembly. Step 1 also names the existing E/F
origin nodes that the current Lean proof already imports.

The current blueprint coefficient-change text has been reorganized since the
historical source path in the parent node. The current compatibility unit still
requires coefficient compatibility with refinement. The new node retains the
recorded blueprint ancestor and identifies auxiliary Step 7 explicitly.

Searches used LeanSearch, LeanFinder, Loogle, and Mathlib grep. They found the
generic mate/unit/naturality tools, including `unit_mateEquiv_symm`, but no
specialized strict refinement restriction theorem. Whole-blueprint search for
"strict refinement" found no matching blueprint node.

## New nodes

`lem-pur-strict-refinement-restriction-squares`, module
`Sheaf.Paper.StrictRefinementRestrictionSquares`, records coefficient restriction
and positive arithmetic selection of the normalized strict refinement map.
Its proof follows auxiliary Step 7 and Stacks 0F7B--0F7D/07A6/0940: preserve the
open unit, clopen projector, ordered proper mate and specified compositors.
The equations are on arbitrary derived strict B-towers and make no faithfulness
claim about separately derived evaluations. Identity refinement, identity scalar
extension, zero tower, empty/full open component, and e=1 specialize to the
respective canonical unit/naturality equations. For e>1, the same maps retain
composite transitions, so no uniform lower bound is assumed. No statement or
definition change record is required: only proofs, private helpers, a private
proof import, and this new theorem/module/node are added.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
