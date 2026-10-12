## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exists_stalk_minimal_complex` by strong induction
on the sum of chosen finite free ranks in degrees 0 through d. The proof handles
zero residue differentials by the identity homotopy equivalence. Otherwise it
applies one cancellation, proves pointwise rank nonincrease and strict decrease
of the finite sum, invokes the induction hypothesis, and composes homotopy
equivalences. The existing statement, universes and visibility are unchanged.

Added `Sheaf.AlgebraicGeometry.FiniteFreeStalkUnitCancellation`, stating one
cancellation with exact adjacent rank drops and unchanged ranks in all other
degrees. This contains the remaining affine free-sheaf matrix comparison,
unit-entry splitting, contraction and transport work. Unlike the original
statement it does not assert existence of a minimal complex or iterate the
cancellation. Updated the original node's proof and proof dependencies accordingly.

Both modules compile together with lcompile.py. The original module also compiled
separately after removing the additional Mathlib tactic and finite-sum imports;
its existing statement imports already make the tactics and sum lemmas available.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_stalk_minimal_complex`
(node `lem-pc-finite-free-stalk-minimal-complex`). There are no sorries remaining
in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation`
(node `lem-pc-finite-free-stalk-unit-cancellation`), in its own new module.
Its proof is exactly `:= by sorry`. This is a decomposition: one hole closed,
one strictly smaller hole added, net zero holes. The termination, finite-sum
inequality and homotopy-equivalence composition are fully proved in Lean.
The original UnitEntrySplits theorem remains an existing dependency; its sorry
is not newly added by this delivery.

No definitions or arbitrary data-valued witnesses were added. All choices of
ranks and homotopy equivalences occur inside the proof of a proposition.

## No longer needed

Removed the direct proof import `Sheaf.Algebra.Homology.UnitEntrySplits` from the
item; its theorem/node `lem-weil-pbc-free-complex-unit-entry-splits` is still
needed through the new cancellation module. It is not pruned from the target
closure. No previously planned node or module is globally pruned. The original
module now needs only the one-step cancellation node as a direct proof dependency.

Temporary additional imports of `Mathlib.Tactic`, `Mathlib.Tactic.Choose` and
`Mathlib.Algebra.Order.BigOperators.Group.Finset` were removed after compilation
confirmed that the existing imports suffice.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically consistent, but its module-valued splitting
lemma does not by itself provide the sheaf-valued homotopy equivalence required
here. Its first affine comparison step and its contraction/transport steps have
no directly matching declared sheaf cancellation interface. These steps are
recorded together in the new one-step node, leaving the iteration proved.

The checkout lacks literature/stacks-project/algebra.tex. The source was read
at [Stacks Tag 00MT](https://stacks.math.columbia.edu/tag/00MT), which supplies the
single unit-entry splitting. Mathlib's Modules/Tilde.lean provides tildeFinsupp,
isoTop and the affine quasi-coherent equivalence; the existing free-sheaf node
records the needed finite-free identifications. No new proof route was taken:
unit sk-thm-picard-perfect is unchanged, and its realized arrays are empty.
The general unit-entry splitting from sk-thm-p1 remains the same generic tool
used by the original plan, not a substitute for this unit's route.

Edge cases checked mathematically: d=0 permits no adjacent degrees in the
support, so the nonzero-residue hypothesis of cancellation is impossible;
zero ranks likewise admit no nonzero map; a residue-zero but nonzero stalk
matrix is already minimal and is returned unchanged; an invertible 1-by-1
matrix cancels to two rank-zero terms; multiple independent unit entries
require repeated applications, which the Lean induction supplies. Cancellation
outside the support cannot occur because a map to or from a zero object is zero.

LeanFinder, Loogle and source grep found no shorter minimal-complex theorem.
LeanSearch returned Internal Server Error; that unavailable service was not
used as evidence of absence. The source library and existing Sheaf modules were
searched for minimal complexes, residue differentials, unit cancellation and
Tag 00MT before adding the new interface.

## New nodes

`lem-pc-finite-free-stalk-unit-cancellation`, in
`dag/nodes/sec-picard-framework/lem-pc-finite-free-stalk-unit-cancellation.json`,
states exactly one cancellation with exact rank changes, a homotopy equivalence,
and preserved bounded support. Its Lean declaration is
`AlgebraicGeometry.Scheme.Modules.exists_stalk_unit_cancellation` in
`Sheaf.AlgebraicGeometry.FiniteFreeStalkUnitCancellation`. The node cites the
existing finite-free tilde identification and unit-entry splitting nodes,
records the full natural-language argument and searches, and inherits the
original chapter, unit and blueprint ancestor. There are no change records or
forced adaptations because no existing interface changed.

## Second reading by V2

1. Compared the delivered minimal-complex module with the repository version. The existing theorem signature is byte-for-byte unchanged; only its proof and proof import changed. The added cancellation module is a new declaration recorded by the new DAG node.

2. Compiled both modules with `lcompile.py --all`. They compile without errors, and the only remaining `sorry` is the explicitly named cancellation theorem. No definitions contain `sorry`, and no forbidden declarations were added.

3. Checked the cancellation statement against the one-step argument and its edge cases (zero support, zero ranks, and a single invertible entry). It is a strict one-step reduction with exact rank changes, rather than a restatement of the minimal-complex target; its source, proof text, and node agree.

4. Reviewed the proof route from the target downward. The induction uses the new one-step cancellation node and composes homotopy equivalences; the unit-entry splitting dependency remains available through that module. Unused direct imports were removed and documented above.

5. Checked the DAG proof, proof dependencies, proof origin, and unit/chapter metadata against the Lean declarations. The unit route is preserved; no target statement or existing interface was weakened.

Changed during second reading: added this required review section only. No Lean code or DAG content required repair.
