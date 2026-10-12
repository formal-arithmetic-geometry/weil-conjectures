## What changed

Retired the false declaration `IsLocalRing.complete_local_domain_finite_over_regular_residue`
from `Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularResidue`. The module now contains
only its module header, public-section marker and retirement comment. The parent module
`Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular` was adapted by removing its two proof
imports and replacing the split composition proof with its original parent `sorry`, while
preserving the parent signature and eight-step source docstring. Its DAG proof and proof
 dependencies record the eight-step construction directly.

## Forced adaptations

`Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular` was the forced adaptation.

The parent originally failed against the changed dependency because the removed declaration
was unknown at the application site (line 166), after the split proof's `obtain` (line 165).
The forced changes are the two private import lines and the proof body; no public signature,
visibility, or docstring line changed. The adapted parent compiles in the delivered sandbox.
The parent is currently unclaimed; the removed declaration was held by X3.

## Proved and sorry left

No theorem is proved in this repair. The invalid split theorem and its `sorry` were removed.
The parent theorem `IsLocalRing.complete_local_domain_finite_over_regular` retains its single
named `sorry` and its original eight-step statement and source proof. The parent's hole was reopened (node
`lem-weil-pbc-complete-local-domain-finite-over-regular`); it was previously filled by
composition through the false split. Thus one invalid holed declaration was retired and
one parent hole reopened: no mathematical theorem was proved, and this is a correctness
repair, not proof progress. No new theorem was split off.

## No longer needed

The imports and declarations of `Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularCore`
and `Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularResidue` are no longer needed by the
parent proof. The split nodes `split-complete-local-domain-finite-over-regular-core` and
`split-complete-local-domain-finite-over-regular-residue`, and their split modules, are
abandoned; the parent construction now depends on its eight-step proof dependencies.
The removed residue declaration had only two textual users: its declaring module and the
parent module. Downstream modules use the unchanged parent interface.

The retired residue module also no longer needs its old proof dependency
`lem-weil-pbc-complete-local-domain-finite-over-regular`. Its now unused public imports
`Mathlib.RingTheory.AdicCompletion.Basic`, `Sheaf.RingTheory.CohenRing`,
`Mathlib.RingTheory.RegularLocalRing.Defs`, and `Mathlib.RingTheory.MvPowerSeries.Basic`
were removed during the second reading.

## Where the brief, the DAG or earlier work was wrong

The retained residue theorem was false for the real subfield of the complex numbers: both
fields satisfy the local, regular, finite, and complete hypotheses, but the induced residue
map is not surjective. Its hypotheses did not carry the special coefficient-ring and power
series construction needed for residue compatibility. The reviewer-requested repair therefore
retires the split rather than retaining a false statement or adding an unusable hypothesis.

## Earlier second reading (a previous round; superseded)

The repaired item and forced parent adaptation compile together. The removed theorem is not
retained, the parent signature and eight-step docstring are unchanged, and the change record
`coord/changes/retire-complete-local-domain-finite-over-regular-residue.md` lists the parent as
an unclaimed forced adaptation and the removed declaration's users.


## Second reading by X3

1. Compared both delivered modules with repository sources. The sole removed signature is
   the explicitly retired false residue theorem, covered by the change record. The parent's
   signature, visibility and eight-step source docstring are byte for byte unchanged. No
   definition or target statement changes. The only user of the removed name outside its
   declaring module is the forced parent adaptation; downstream interfaces are preserved.
2. Both delivered modules compile through lcompile.py. The only remaining hole is
   `IsLocalRing.complete_local_domain_finite_over_regular`, with its existing source proof
   and DAG node. There are no definitions, forbidden declarations, or hidden holes in the
   delivery. The parent's axiom print contains the three permitted logical axioms and
   `sorryAx`, as expected for the reopened theorem. Independently recompiled the scratch counterexample: the real subfield of the
   complex numbers satisfies all the retired hypotheses, but compatibility plus
   surjectivity would force the imaginary unit to be real. Its axiom print uses only the
   permitted logical axioms.
3. No new statements or nodes are split off. The removed arbitrary-subring assertion is
   false even for complete regular local fields, so a shorter sound proof cannot exist.
   Searched the library for residue surjectivity and Cohen structure; existing coefficient
   subring results require extra construction data absent from the retired theorem.
4. The parent no longer depends on either core/residue split; both are reported as pruned.
   Removed all four unused imports of the empty retired module. The unit
   `dag/units/sk-thm-p1.json` has neither split in its realized statement or steps; its
   curve-calculation and strictly-henselian comparison route is preserved. This delivery
   restores a hole rather than pretending that deleting a false statement proves it.
5. The residue node has no Lean realization or proof dependencies. The parent node keeps
   its original statement and Lean realization, and restores the eight-step construction
   from its retained docstring; proof_deps is exactly the union of those steps' uses.
   These steps are a plan for the reopened hole, not a claim of a completed Lean proof.

Second reading changed the retired module's unused imports and empty namespace scaffolding,
updated the change record accordingly, and made the reopened-hole accounting explicit.

## Forced adaptations

### Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
Original against changed dependencies failed:
```
/tmp/forced-adaptation-0ln7w989/lean/Sheaf/RingTheory/CompleteLocalDomainFiniteOverRegular.lean:166:8: error(lean.unknownIdentifier): Unknown identifier `complete_local_domain_finite_over_regular_residue`
/tmp/forced-adaptation-0ln7w989/lean/Sheaf/RingTheory/CompleteLocalDomainFiniteOverRegular.lean:165:13: error: Tactic `rcases` failed: `x✝ : ?m.125` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-0ln7w989/.lbuild) [1.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
