## What changed

Completed the proof of `AlgebraicGeometry.alternatingCechSheaf_restrict_differential_inner_inverse`
without changing its signature or its existing docstring. The only new proof import is
`Sheaf.AlgebraicGeometry.AlternatingCechPresheafPositiveInsertion`.

The proved private helper `alternatingCechSheaf_restrict_natural_insertion` applies additive
sheafification and restriction to a presheaf insertion equation. It uses the already proved
`cechCapPresheafUnit_local_isIso`, naturality, and cancellation of two local unit isomorphisms.
The main proof precomposes this identity with a differential, uses `d_comp_d`, and conjugates
through `extendXIso` using `extend_d_eq`. Negative degrees are proved directly using
`isZero_extend_X`, `map_isZero`, and the zero morphism.

The new module states only the remaining positive-degree presheaf signed insertion identity.
Its source, complete coordinate argument, sign pairing, and edge cases are in its docstring
and new node. The original node now records the actual Lean proof route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.alternatingCechSheaf_restrict_differential_inner_inverse`
(node `lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse`).
The item's module has no remaining `sorry`.

Added one hole:
`AlgebraicGeometry.alternatingCechSheafPresheaf_positive_insertion`
(node `lem-pc-s3-alternating-cech-presheaf-positive-insertion`). Its entire proof is `by sorry`.
This is a decomposition: one original hole closed, one strictly lower presheaf identity added,
net zero holes. The new statement is not the original under another name or with an extra
hypothesis: it states a two-term cancellation equation with different source and target
presheaves. The sheafification, inner-inverse deduction, integer transport and negative-degree
case are all proved here. No arbitrary existence witness supplies definition data.

## No longer needed

No existing library import, module or dependency node is pruned. The construction remains
necessary. The saved attempt's `AlternatingCechSheafDifferentialInnerInverseNonnegative`
module and matching uncommitted node were removed from the sandbox: they only repackaged the
original statement with a nonnegative-degree hypothesis. Its duplicate top-level Lean file
was also removed. These were never library nodes and do not count as library pruning.

No import of `AlternatingCechSheafPositiveContraction`, `AlternatingCechSheafInsertionIdentities`,
or `AlternatingCechSheafInsertionHomotopy` is added: all reach this item already, as checked by
`tools/import_direction.py`. The degree-zero presheaf insertion module is not needed.

## Where the brief, the DAG or earlier work was wrong

The saved report claimed that the negative-degree case was proved, but that helper still
contained `sorry`. Its new module's docstring referred to the original blueprint node, its
new node recorded an abbreviated Lean signature rather than the verbatim statement, and the
original node had not been updated. This attempt replaces that unfinished split entirely.

The existing DAG route is mathematically valid and the unit's route is preserved. A useful
proved transport lemma is now available in `CechCapPresheafLocalIso`, so no separate proof that
every intersection presheaf is a sheaf is needed for the transport. Local cap-unit invertibility
works even for arbitrary presheaves.

Edge cases checked: r=0 has no i; r=1 and p≥0 have zero positive terms; empty opens yield zero
modules; above the maximum tuple length the same equations hold; k=-1 has zero source despite
possibly nonzero target. Signed insertion at a tuple containing i uses only deletion of i;
for a tuple omitting i the two other face exponents differ by one.

## New nodes

`lem-pc-s3-alternating-cech-presheaf-positive-insertion`, in
`dag/nodes/sec-picard-framework/`, states the positive-degree signed insertion equation before
sheafification. Its module is `Sheaf.AlgebraicGeometry.AlternatingCechPresheafPositiveInsertion`.
It is the sole residual hole and is strictly the coordinate-construction/cancellation part of
the original plan. The existing parent node is updated only in proof-owned fields.
No statement, definition, public import, or other group's module is adapted.

## Second reading by H3

1. I compared the delivered item module with the repository version. The target theorem's
   signature and docstring are byte-for-byte unchanged; only its proof and a proof-only import
   were added. The new module has the exact statement recorded in its node.
2. Both sandbox modules compile with `lcompile.py --all`. The target has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`; the sole remaining `sorry` is the named
   split theorem and is documented by its source and coordinate proof. The target proof uses
   only the permitted kernel axioms apart from that imported split theorem.
3. The split statement is a genuine lower presheaf identity: it changes the source and target
   presheaves and isolates the coordinate sign cancellation, so it is true and strictly simpler
   than the target. Repository and Mathlib searches found no existing declaration of it.
4. The proof follows the unit route through local cap-unit isomorphisms, sheafification,
   differential-square cancellation, and integer extension. No proof-dependency import was
   removed; the new import is private to this proof. The discarded nonnegative wrapper was a
   duplicate and is not delivered.
5. The parent and new DAG nodes match the Lean declarations and proof dependencies. The unit's
   realized route is preserved; the parent node's proof fields now describe the actual H3 route.

I changed only the proof of the existing target, added the proof-only presheaf import, added the
strictly lower split module and node, updated the parent's proof-owned DAG fields, and added this
second-reading record. No public existing statement or definition was changed.
