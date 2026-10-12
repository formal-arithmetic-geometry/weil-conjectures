## What changed

Reduced `CategoryTheory.Functor.rightDerivedBaseChange_single_unit_homology` in
`Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnitHomology` without changing its signature.
Added a proof-only import of `Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnit`.
The new intermediate theorem states the derived equation before taking homology, the first
step of the original proof plan. The main proof applies H⁰, uses homology-comparison naturality,
cancels the single-complex homology isomorphism, and applies inverse-comparison naturality.
Both node proof records now agree with this reduction.

## Proved and sorry left

Accounting: one original local hole closed, one new local hole added; net zero.
This delivery is a decomposition, not an axiom-free proof of the original theorem.
Of the one original holed theorem, zero are proved without `sorryAx`.
The homology and cancellation portion of its argument is now proved.

`CategoryTheory.Functor.rightDerivedBaseChange_single_unit_homology`
(node `lem-sbc-right-derived-base-change-single-unit-homology`) has no sorry in its proof.
The only new sorry is `CategoryTheory.Functor.rightDerivedBaseChange_single_unit`
in `Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnit`, node
`lem-sbc-right-derived-base-change-single-unit`. It is the pre-homology transport step,
not a renamed homology statement: the homology comparison and cancellation argument is proved
in the original module. The unchanged sandbox copy of
`RightDerivedSingleUnitHomologyComparison.lean` is only needed by the local compiler because its
object file was initially absent; it is not a changed delivery module. Its existing
`rightDerivedPlusSingleUnitHomology_comp_comparison` sorry is untouched and not used here.

## No longer needed

No original imports were removed: both public imports provide declarations used by the
unchanged statement. No original proof dependency was pruned. The classical augmentation
comparison `rightDerivedPlusSingleUnitHomology_comp_comparison` and the classical
`rightDerivedBaseChange_zero_unit` equation are not needed in this proof; the argument does
not require left exactness of G or G′. No additional planned module is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original first proof step includes substantial
coherence work for Qh, exact-functor single-complex comparisons, and unit naturality. That
step is isolated as a public theorem with the same generality and a detailed proof plan.
The edge cases e = 0, identity functors, and a zero object are consistent: all sides reduce
to zero or ordinary unit naturality. The unit record sk-prop-deg0 has no realized nodes that
this reduction bypasses. The local compiler lacked the existing comparison module object;
compiling an unchanged sandbox copy enabled local testing.

## New nodes

`lem-sbc-right-derived-base-change-single-unit` in
`dag/nodes/sec-smooth-base-change/lem-sbc-right-derived-base-change-single-unit.json` records
step one of the original plan before homology. Its new module is
`lean/Sheaf/CategoryTheory/RightDerivedBaseChangeSingleUnit.lean`; its source is
`rightDerivedFunctorPlusBaseChange_fac`. No change records are required: existing statements
and definitions are unchanged.

## Second reading by H2

1. Unchanged interfaces: PASS. Diffed both existing sandbox modules against the
   repository. The comparison module is byte-for-byte unchanged. The item's only
   changes are its proof body and a plain proof-only import; the declaration
   signature, section assumptions, public imports and definitions are unchanged.
   No change record is needed.
2. Kernel check: PASS for a decomposition. Compiled all three files in import
   order with lcompile.py, without errors or warnings. A scratch copy with
   #print axioms shows propext, Classical.choice, Quot.sound and sorryAx for
   the original theorem and the new intermediate theorem. The unit and homology
   unit definitions use only the three permitted axioms. The only new sorry is
   rightDerivedBaseChange_single_unit; the comparison module's existing
   rightDerivedPlusSingleUnitHomology_comp_comparison remains untouched.
   No forbidden declaration, hidden axiom, or hollow definition is present.
3. Split statement: PASS. Checked its arrows and the orientations of the unit,
   exact-functor single comparisons and Qh transports against their definitions
   and rightDerivedFunctorPlusBaseChange_fac. At e = 0 both composites vanish;
   for identity functors the equation is unit naturality, and at a zero object
   both sides are zero. The intermediate statement isolates the original
   pre-homology transport step: the remaining homology naturality, isomorphism
   cancellation and naturality on e(Y) are proved in the item. Its source and
   docstring describe the transport proof, and its separate node records it.
   Independent leanfinder search for unit naturality under an exact square,
   loogle search for NatTrans.naturality and grep searches, plus rg across the
   library's unit and base-change declarations, found no duplicate single-unit
   equation. The generic localization results do not remove this coherence step.
4. Route and pruning: PASS. Read the full proof from its target downward: apply
   H0 to the split equation, move the source unit by comparison naturality,
   cancel the single-complex homology iso, then use inverse-iso naturality on
   e(Y). Both original public imports are required by the unchanged signature;
   the new import is proof-only. The sole old proof dependency,
   lem-sp-exact-functor-preserves-homology, is still used, so nothing is pruned.
   sk-prop-deg0.realized has empty statement and step lists; no realized unit
   route is bypassed. The new coherence theorem was not closed in this reading.
5. Nodes: PASS. The existing node changes only proof, proof_deps and
   proof_origin, and names the split equation and homology compatibility used
   by the Lean proof. The new node's statement matches its Lean declaration,
   and it includes source, proof steps, origin, three search kinds, creation,
   blueprint parent, chapter, unit and Lean record as required.

Changes by this reader: corrected the report to distinguish a one-for-one
hole decomposition from an axiom-free proof; recorded independent searches,
compilation, axiom checks and the five review verdicts. No Lean proof,
statement, definition or import needed repair. Removed the scratch axiom probe
before delivery; retained the unchanged comparison copy for local compilation.
