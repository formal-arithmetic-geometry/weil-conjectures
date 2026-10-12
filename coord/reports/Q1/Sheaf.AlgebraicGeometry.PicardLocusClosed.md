## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.picard_locus_closed` with the
closed-image valuative criterion, installing its immersion and quasi-compactness
instances from `hj`. The new module
`Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization` states the
remaining local extension argument. This helper assumes only the universal
factorization property of `j`, without immersion, finite presentation,
quasi-compactness or quasi-separatedness of `j`. The target passes that property
as `hj.the project server`. All existing signatures and public imports are unchanged.

The helper's docstring explains base change, the structure-sheaf unit's effect
on generic global sections, the rank-one argument over the fraction field,
Tag 0EX8, and the final application of the universal property. Its proof-plan
import of valuation triviality is private. The target node now records the
actual closed-image criterion plus local factorization reduction.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.picard_locus_closed`
(`lem-sc-picard-locus-closed`).
Hole added: `AlgebraicGeometry.Scheme.picard_valuative_factorization`
(`lem-sc-picard-locus-closed-valuative-factorization`).

This is a decomposition, not a completed axiom-free proof: one original hole
closed, one new hole added, net zero. The original target has no textual
`sorry`, but still depends on `sorryAx` through its prerequisites. No definition
or unnamed proof contains a new hole. The helper is strictly the local
valuation-ring extension step; the target combines it with the separately
stated closed-image criterion. The helper does not assume closed immersion or
any immersion/finiteness properties of `j`.

## No longer needed

Removed the target's private import of
`Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality`; moved it to the
helper, whose remaining argument needs it. The old direct proof dependency
`lem-sc-picard-locus-closed-valuation-triviality` is now transitive through the
helper, so its module is not pruned from the import closure.

The old direct proof dependency `lem-sc-picard-diagonal-locally-closed` is no
longer invoked by the proof: its full conclusion is supplied as `hj`. It remains
a statement dependency and its existing public import remains for compatibility.
The helper directly imports `TensorPullbackAdjunction`, which supplies the
adjunction declaration appearing in its signature, instead of publicly
importing `PicardDiagonalLocallyClosed`. Removed the helper's unused explicit
ClosedImmersion and Immersion imports. The valuation criterion dependency stays.
No entire module is claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The first worker's helper docstring did not give a complete proof in words.
Its node copied historical review, split-report and Lean-audit fields from the
original node, falsely suggesting this new statement had already been reviewed.
The delivery omitted the existing target node's proof update. All three faults
are repaired. The initial report described a proof without clearly counting the
one-for-one decomposition; the accounting above corrects this.

## New nodes

`lem-sc-picard-locus-closed-valuative-factorization` records the local extension
step of Stacks Tag 0BF0 using Tag 0EX8. Its stronger local formulation does not
need the immersion or finiteness hypotheses on `j`. Its Lean statement is
recorded verbatim modulo whitespace, its sole non-elementary proof dependency
is the valuation-ring triviality lemma, and it has independent search records.
No existing statement or definition changed; no change record is required.

## Second reading by Q1

1. Compared the delivered target with the repository using `diff`: the only
   changes are its proof and private imports. Its existing theorem signature
   is byte-for-byte identical; no definition, target statement, existing public
   import or declaration visibility changed. Verdict: pass.
2. Compiled both modules in import order with `lcompile.py --all`. They compile
   without errors or warnings. Checked for forbidden declarations and data
   holes; the only new `sorry` is the named helper listed above. Scratch
   `#print axioms` checks for target and helper show only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Verdict: valid decomposition,
   not a finished axiom-free proof.
3. Checked the helper against Stacks Tags 0BF0 and 0EX8. Its generic fibre is
   nonempty by geometric integrality, which is essential to force the finite
   locally free module over the field to have rank one. Field valuation rings
   cause no exception (the fraction-field base change is an isomorphism);
   empty base schemes admit no valuation square, while an empty fibre over a
   field violates geometric integrality. The identity family gives the expected
   trivial factorization. The new theorem does not restate closed immersion:
   it proves the local extension step, with fewer hypotheses on `j`, and the
   target separately applies the closed-image theorem. Repeated searches with
   different terms using leanfinder, loogle, grep, and local `rg`: no exact
   existing extension theorem found. The generic triviality theorem already
   exists and remains the planned prerequisite. Verdict: true and needed;
   too much base-change/rank-one API work to close in a few minutes.
4. Checked the top-down reduction and direct imports. The existing criterion
   supplies the global closed-image step; the remaining hole is local. Removed
   the unused direct valuation-triviality import and redundant helper imports,
   as documented above. `dag/units/sk-prop-av-cube.json` has empty realized
   entries; no unit realization or chapter route is bypassed or altered.
   Verdict: pass; no whole-module pruning claimed.
5. Read both nodes with the Lean source open. Updated the existing target's
   proof and proof_deps to match the implementation; its document proof_origin
   still identifies Tag 0BF0. The new node has its independent provenance,
   searches, source, complete local proof plan, required creation/Lean fields,
   and exact signature. Removed inherited review/audit history. Verdict: pass.

Second reading changed the helper's unused hypotheses and imports, its complete
proof docstring, the target's private imports and helper application, both node
records, and the report's decomposition/pruning accounting. No existing
statement was changed.
