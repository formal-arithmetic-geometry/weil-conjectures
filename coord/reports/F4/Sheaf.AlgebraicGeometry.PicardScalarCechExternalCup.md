## What changed

In lean/Sheaf/AlgebraicGeometry/PicardScalarCechExternalCup.lean, replaced the
application of the false uncovered core by a complete Lean proof of
AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup with its statement
unchanged. The proof eliminates the degree equality, obtains the three ordinary
comparison witnesses, chooses the uniquely characterized module cup, maps the total
cycle with cyclesMap, and uses the prescribed bidegree coordinates. The existing
picardModuleCech_externalPairing computes the ordinary class using both covers.
Homology projection naturality and scalarExternalCup_moduleComparison finish the
scalar equality. Added plain proof imports of PicardModuleCechExternalPairing and
ScalarExternalCupModuleComparison; the two public imports are unchanged.

Withdrew AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core;
see coord/changes/picard-scalar-cech-uncovered-core-withdrawal.md. Updated both
existing nodes: the cover theorem's proof follows its Lean assembly, and the false
core's Lean attachment is removed with null. No new module or node is added.

## Proved and sorry left

Hole accounting: no original sorry is closed by proving that declaration; the sole
original sorry is the false core, which is retired. No holes are added. The cover
theorem already had a proof body on the baseline, but that body applied the false
core; this delivery repairs that proof. This is a repair, not a new axiom-free
closure of the theorem.

The retained cover theorem AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup
(lem-sc-picard-scalar-cech-external-cup) now has a complete Lean proof independent
of the uncovered core. The sole original hole,
AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core
(lem-sc-picard-scalar-cech-external-cup-core), is withdrawn because it is false;
this is pruning an invalid split, not a proof of that false statement. There are
zero sorry declarations in the delivered module and zero holes added or split off.
The imported existing statements scalarCup_moduleCup_compatibility and
scalar_moduleCohomologyPullback_comparison remain separate existing obligations;
this delivery adds no such obligations. Compiled the changed module with lcompile.py
in about 12 seconds, and tested all three used project theorem imports with
#print axioms before assembling the proof. The required dry run printed OK and completed the
compile and axiom/sorry probe, with no duplicate-instance import failure. Also
compiled the original, unchanged direct importer
Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison against the changed
module in the sandbox overlay (about 22 seconds); its temporary source copy is
removed from the delivery. No consumer adaptation is needed.

## No longer needed

Removed the plain import Sheaf.Paper.CechCupPullbackCompat and its direct proof
edge lem-sc-picard-cech-cup-pullback-compat. The cover theorem no longer uses the
false node lem-sc-picard-scalar-cech-external-cup-core or its declaration.
The module CechCupPullbackCompat remains publicly reachable through existing
statement imports, so this import removal is not claimed as removal of the whole
module from the target closure. The old direct edges def-sc-cech-refinement-cochain-map,
def-sc-cech-cup-product and def-sc-field-linear-module-cohomology-operations are
now reached through the existing interfaces and module pairing. They are not
claimed as globally pruned nodes. The exact assembly keeps direct edges to
lem-sc-picard-scalar-cech-comparison, lem-sc-picard-external-cech-cup-component
and def-sc-module-cohomology-cup-product, and adds direct edges to
lem-sc-picard-module-cech-external-pairing and
lem-sc-scalar-external-cup-module-comparison.
The unit sk-prop-av-cube has no realized entry for either affected node; its statement
and steps stay intact, and only the below-unit assembly changes.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: picardScalarCech_externalCup_core is false because it omitted
cover equalities. The comparison equation c followed by H(alpha) equals H(beta)
only determines c when H(alpha) can be cancelled. For non-covers it allows arbitrary
kernel-valued additions; these need not preserve products. The change record gives
a counterexample using the pushforwards of O(-2) from two disjoint fibres in
P1 times P1, two opens covering just one fibre, and cup with the unit on Spec k.
This also addresses the earlier ledger reviews flagging the false core. The retained
cover theorem uses hUc and hVc through picardModuleCech_externalPairing; neither
hypothesis is discarded. Stacks Tag 01FD and Tag 0FKV both require coverings:
[Tag 01FD](https://stacks.math.columbia.edu/tag/01FD) and
[Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV).

The F4 dedicated repair handoff reports a duplicate-instance import/probe failure.
On the current published library the existing ordinary-pairing, scalar-comparison,
and module-cup imports compile together, including their axiom queries. This proof
uses those current declarations and adds no copy of the previously split module
or an instance. The dry run also completed its probe; no changes to an instance module are
needed on this published snapshot.

## Second reading by F4

1. Interfaces: PASS. Compared the sole delivered Lean module with the repository
   using diff and independently checked the retained theorem signature byte for
   byte. Its hypotheses, conclusion, visibility, and both public imports are
   unchanged. There are no definitions to alter. The only withdrawn declaration
   is picardScalarCech_externalCup_core, explicitly recorded in the change record.
   A search of all Lean sources finds no external reference to that core; the
   original direct importer compiles unchanged against the delivered module.

2. Proof: PASS, conditional on existing upstream obligations. Independently
   compiled the module without errors or warnings. A scratch copy with
   #print axioms picardScalarCech_externalCup reports precisely propext,
   Classical.choice, Quot.sound, and sorryAx. The latter comes from existing
   upstream statements, not a local hole; exists_unique_moduleCupProduct also
   has this dependency. There is no local sorry, axiom, unsafe, opaque,
   implemented_by, extern, or skipped kernel check. The mapped cycle is
   constructed with cyclesMap. The cup witness is uniquely characterized, and
   is used only inside a theorem proof; no arbitrary data is defined from an
   unproved existence assertion.

3. Split statements: PASS (none added). Read the actual comparison predicate:
   without a covering, the alpha equation cannot cancel the kernel of restriction
   to the union. Checked the change record's example: the two indicated opens
   cover C0 but miss Cinf, so H1 of the Cech complex is k while global H1 is k².
   Restriction projects onto the first coordinate, admitting both displayed
   lifts. Cup with the unit on Spec k distinguishes the independently chosen
   factor and product lifts. Thus withdrawal of the uncovered core is justified.
   The retained proof handles degree zero, zero coefficients, and empty schemes
   through the same ordinary pairing; it imposes no new nonemptiness assumptions.

4. Route and pruning: PASS. Read the ordinary external pairing, scalar external
   comparison, scalar Cech comparison, component predicate, and unique module
   cup interface. Repeated searches with msearch grep, loogle, and leanfinder
   locate the Mathlib cyclesMap_i and homologyπ_naturality used here, but no
   shorter theorem providing this project-specific scalar compatibility. Both
   added imports are plain proof imports and used; both public imports are needed
   by the signature. No longer needed enumerates all removed old proof edges
   and distinguishes removal of the direct import from global module pruning.
   The unit sk-prop-av-cube has no realized entry for either affected node;
   its statement and proof steps are unchanged. Checked the cited
   [01FD](https://stacks.math.columbia.edu/tag/01FD) and
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV) statements: both assume covers.

5. Nodes: PASS. The retained node's four proof steps and proof_deps union match
   the Lean assembly: comparison witnesses, unique cup, constructed image cycle
   and ordinary pairing, then scalar comparison. The retired node has its Lean
   attachment cleared and obsolete proof edges removed, with the dispute and
   withdrawal recorded in proof_origin. Other existing node fields and statements
   are unchanged. No new nodes require validation.

Second reading changed only this report: added the independent checks and made
hole accounting and remaining upstream sorryAx dependencies explicit. The Lean
proof, node edits, and withdrawal record required no repair.
