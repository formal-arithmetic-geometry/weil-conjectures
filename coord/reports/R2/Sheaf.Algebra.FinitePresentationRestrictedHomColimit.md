## What changed

Proved `ModuleCat.exists_stage_restricted_hom` in
`Sheaf.Algebra.FinitePresentationRestrictedHomColimit`, with its signature and visibility unchanged.
Added the proof-only imports `Sheaf.Paper.DirectedColimitBaseChangeElementwise` and
`Mathlib.Data.Fintype.Order` (the latter supplies finite upper bounds).
A proved private helper `ModuleCat.lift_finitePresentation` carries out finite-generator lifting,
eventual vanishing of finite relations, and quotient descent for a directed module system.
The public proof constructs the tensor system on the upper tail, applies that helper, and proves
comparison compatibility by tensor induction and balancing. Updated the existing node's proof,
proof dependencies and proof origin to match. No definitions or public interfaces changed.

Searches: Lean Finder returned direct-limit constructions, Loogle returned finite-presentation
basics, and grep found no ready-made finite-presentation factorization theorem. The existing proved
`TensorProduct.directedColimitBaseChangeElementwise` supplies exactly the required element lifting
and eventual zero. Local single-file compilation passes without warnings. Empty generator and
relation sets use the finite-upper-bound lemma on the nonempty upper tail; no nonzero module or
finite-presentation hypothesis on N is added.

## Proved and sorry left

Closed the sole original hole: `ModuleCat.exists_stage_restricted_hom`
(node `lem-pc-fp-restricted-hom-colimit`). The private helper is fully proved as well.
No sorries remain in the item, and no holes were added or split off. The only Sheaf proof dependency
is already proved; the dry-run axiom probe checks the resulting declaration and its helper.

## No longer needed

The direct dependencies `lem-pc-finite-tensor-vanishing-colimit`
(`Sheaf.Algebra.FiniteTensorVanishingColimit`) and
`lem-pc-filtered-colimit-commrings-elementwise` are no longer needed as separate steps of this
module's proof. The former was not imported in the assigned source; the latter is a Mathlib leaf,
not a Sheaf module. Ring representative/equality facts are still used internally by the proved
elementwise tensor theorem. No existing import was removed. `Mathlib.Data.Fintype.Order` is needed for finite upper bounds. All three original public
Mathlib imports remain for the existing interface. This pruning is local to this item's route:
other consumers may still need the finite-tensor-vanishing module. The unit has no realized nodes
here, and its statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The plan's two lower dependencies are superseded here by
the stronger already-proved tensor elementwise theorem, which covers arbitrary module universes.
In particular, this avoids the same-universe restriction in the finite-tensor-vanishing interface
without changing or adapting it. No new nodes or forced adaptations.
The cited local Stacks source is absent on this machine; checked the published
[Tag 05LI](https://stacks.math.columbia.edu/tag/05LI), proof of (3), which gives precisely
the finite-generator/finite-relation argument used here.

## Second reading by R2

1. Compared the delivered module with the repository version. Existing declaration signatures,
visibility, and definitions are unchanged; only proof code and proof-only imports differ. Verdict: pass.
2. Compiled with `lcompile.py` and searched for forbidden constructs. Compilation is clean; there are no
`sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. A scratch-copy
`#print axioms ModuleCat.exists_stage_restricted_hom` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, also certifying its helper transitively. Verdict: pass.
3. Checked the finite-presentation lifting argument against the existing library theorem and Stacks
source. The statement is true and unchanged, with no split-off statement or new node. Verdict: pass.
4. Reviewed pruning and imports. The tensor elementwise directed-colimit theorem supplies the
representation and eventual-vanishing clauses; the finite-presentation helper handles generators
and relations. The unit statement and route remain unchanged. Verdict: pass.
5. Compared the DAG proof metadata with the Lean proof. The proof steps, dependency, and origin match;
the realized unit record is unaffected. Verdict: pass.

Second reading changed only this report by adding the independent review and axiom-check evidence.
No proof repair was necessary.
