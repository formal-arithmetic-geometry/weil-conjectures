## What changed

The original theorem is reduced to the geometric separable-polynomial step in the new
module `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial`.
Its statement is unchanged. The final splitting and root-image argument is proved in Lean
using `IsSepClosed.splits_of_separable` and `Polynomial.Splits.mem_range_of_isRoot`.
The sandbox compiles with lcompile.py --all. The new lemma does not assume that κB
is separably closed; that assumption is used only in the proved splitting step.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_image`.
Added: `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_separable_polynomial`
(node `lem-weil-pbc-compatible-strict-henselization-residue-polynomial`).
This is a decomposition: one hole closed, one geometric hole added, net zero.
The new hole establishes a separable polynomial; the polynomial splitting and conversion
of a mapped root to a residue-field preimage are proved here.
Edge cases: x=0 has polynomial X; x=1 has X-1. No zero polynomial is allowed.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples` and
`Sheaf.RingTheory.StrictHenselizationTriples` from the item; they remain dependencies of the
geometric polynomial lemma. The old proof dependencies
`lem-weil-pbc-etale-local-ring-triples` and `lem-weil-pbc-strict-henselization-triples`
are no longer direct dependencies of the item, but are retained by the polynomial node.
`def-pc-separably-closed` remains a direct dependency. Removed the redundant
`Mathlib.FieldTheory.IsSepClosed` import from the new module (already publicly imported
by `WeilConjectures.Mathlib.RingTheory.Henselian`). No existing module or node is pruned
from the closure.

## Where the brief, the DAG or earlier work was wrong

The final part of the DAG's step 3 is already available from Mathlib's splitting/root-image
API. Its earlier geometric coefficient-transport part remains the new item.
The local Stacks source file is absent; Tags 04HX and 095T were read at
https://stacks.math.columbia.edu/tag/04HX and https://stacks.math.columbia.edu/tag/095T.
The first worker reported a dry-run request for a second-reading section; the second
reader supplies the completed section below.

## New nodes

`lem-weil-pbc-compatible-strict-henselization-residue-polynomial` records the coefficient
transport and separability step. It does not assert or choose a residue-field preimage.


## Second reading by F1

1. **Interfaces: pass.** Diffed the existing module against the repository. The existing
   declaration signature is byte-for-byte unchanged, including its hypotheses and
   conclusion. No definition, existing docstring or public import changed. The only new
   declaration is the polynomial lemma, with its own module and node; no change record is
   needed for a new declaration. No target statement changed.
2. **Proof and axioms: pass as a decomposition.** Compiled both modules in import order
   using lcompile.py --all (3.1 s and 2.9 s, no warnings). A scratch copy with #print axioms
   for both declarations reported only propext, Classical.choice, Quot.sound and sorryAx.
   The only delivered sorry is the named polynomial theorem listed above. There is no
   axiom, unsafe, opaque, implemented_by, extern or holed definition. The polynomial
   witness is eliminated within a proposition, never chosen to define data.
3. **Split-off statement: pass.** Read the complete signatures, residue-triples theorems
   and the sources [Stacks 04HX](https://stacks.math.columbia.edu/tag/04HX) and
   [Stacks 095T](https://stacks.math.columbia.edu/tag/095T). The geometric step transports
   a monic separable polynomial over κ(s) along κ(s) → κ(t) → κB. Compatibility of these
   residue maps follows from hι, hρA and hρB. Mapping preserves monicity and separability,
   so the required polynomial is nonzero and has the specified mapped root. Tested x=0
   with X and x=1 with X-1, also in positive characteristic. A zero polynomial is excluded;
   a nonzero constant cannot have the specified root. No perfectness assumption is needed.
   Removed the unnecessary IsSepClosed κB hypothesis from the new lemma: its conclusion
   is the separable-polynomial step, whereas splitting and root-image containment are
   proved in the item. This is a genuine partial argument, not an application of a renamed
   containment theorem. Fresh leanfinder, loogle and grep searches with different wording
   found Algebra.IsSeparable.isSeparable and Polynomial.Separable.map, which implement
   only the field-theoretic parts. Searching lean/ and the upstream algebraic geometry
   sources found no existing theorem supplying the model-specific coefficient compatibility.
   The new docstring now spells out the residue-map equation and polynomial construction.
   Closing the remaining geometric theorem requires the nontrivial colimit/model transport;
   no replacement in Mathlib or a short complete proof was found.
4. **Route and pruning: pass.** The final splitting and root-image argument already uses
   Mathlib's shortest direct route. All remaining public imports support signatures; all
   geometric proof imports are plain imports. Removed one redundant public import from
   the new module. The two old geometric dependencies move behind the new lemma, so no
   existing module leaves the target closure. The old dependencies are all accounted for
   under No longer needed. Checked dag/units/sk-thm-p1.json realized: the item is below
   those realized nodes, and this decomposition retains the strict-henselization route
   in the arbitrary-base step without bypassing any unit statement or step.
5. **DAG: pass.** Checked the item node's proof, proof_deps and proof_origin against the
   actual polynomial/splitting/root-image proof. Checked the new node's statement verbatim
   against Lean, its source, complete proof steps, dependency union, three search kinds,
   creation record, blueprint origin, chapter, unit and lean record. Updated the new node
   for removal of the κB separable-closedness hypothesis. Existing node edits are confined
   to the stage-3-owned fields.

Second reading changed: removed the new lemma's unused IsSepClosed κB hypothesis;
expanded its docstring with the precise compatible residue-map equation; removed its
redundant Mathlib.FieldTheory.IsSepClosed import; restored original signature spacing;
updated the new node and clarified dependency/pruning accounting in this report.
This remains one upper hole closed and one strictly geometric hole added, net zero.
