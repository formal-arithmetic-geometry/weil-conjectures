## What changed

Reduced AlgebraicGeometry.properSupport_local_noetherian_model without changing its
signature or any definition. The proof chooses an affine neighbourhood, constructs
the concrete filtered diagram of finitely generated Z-subalgebras of its section
ring, proves that every stage is Noetherian, invokes the existing simultaneous
noetherian_approximation_data theorem, and composes the two comparisons and the
proved derived-pullback composition isomorphism.

Four new modules separate the argument:

- ProperSupportAffineTensorRestriction explicitly constructs the canonical pullback,
  its perfect object and its termwise pulled complex. Its proof verifies the
  original bounds using additivity, invokes the termwise properties, and proves
  its direct-image comparison using the cartesian comparison and pullback composition.
- ProperSupportTensorPullbackProperties proves finite presentation by identifying
  tensor pullback with native pullback through uniqueness of left adjoints. It
  proves proper support by the already-proved support-pullback equality, a pasted
  cartesian square of the reduced support, proper base change, and independence
  of properness from the closed subscheme structure.
- RelativelyFlatModulePullback isolates relative flatness of an individual module
  under an arbitrary scheme base change; its complete stalkwise proof is recorded.
- CartesianTensorDataComparison isolates transport of relatively flat tensor
  comparison to a specified cartesian square and specified factor identifications.
  It uses ordinary pullback on the second tensor factor, as the source requires.

The relative-flatness step assumes quasi-coherence, supplied by finite presentation
at its caller; this is required for the affine-section/stalk equivalence of Tag 01U4.

All new modules are module-system files. The original module keeps every public
import and adds only proof imports. No downstream adaptation or change record is
needed. The item node and four new nodes record the actual route. The fixed unit
route is preserved (its realized arrays contain no nodes bypassed here).

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.properSupport_local_noetherian_model
(lem-pc-proper-support-local-noetherian-model).

Also proved the two new argument steps:
AlgebraicGeometry.properSupport_affine_tensor_restriction
(lem-pc-proper-support-affine-tensor-restriction) and
AlgebraicGeometry.properSupport_tensorPullback_properties
(lem-pc-proper-support-tensor-pullback-properties).

Exactly two new holes remain, each a public named theorem with the entire proof
`:= by sorry`, a matching node, a source and a full proof in its docstring:

- AlgebraicGeometry.relativelyFlat_module_pullback
  (lem-pc-relatively-flat-module-pullback).
- AlgebraicGeometry.cartesian_tensor_data_comparison
  (lem-pc-cartesian-tensor-data-comparison).

This is a decomposition: one pre-existing hole closed, two holes added, net -1.
The original module has no remaining sorry. noetherian_approximation_data and
relativelyFlat_tensor_baseChange_iso are existing dependencies, not new holes.
No direct-image perfectness theorem is used. No witness from an unproved existence
statement is used to define data in a definition; the new constructions occur only
inside proofs of propositions.

Verification: all five modules compiled together in import order with lcompile.py,
without errors or warnings. The delivery dry run also performs its axiom probes.
The empty-base case has no x. Empty supports and zero complexes are covered by
support inverse-image equality, additive preservation of zero terms and the same
functorial comparisons; arbitrary nonflat base changes use relative flatness only.

## No longer needed

Removed direct proof imports from the original module:

- Sheaf.AlgebraicGeometry.DerivedPullbackPerfect: used inside the new affine step.
- Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso: retained as a proof
  dependency/import of CartesianTensorDataComparison.
- WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit: the original proof
  only needs its narrower ring-colimit module directly. The spreading-out theorem
  thm-pd-spreading-out remains below noetherian_approximation_data.

None of these is claimed globally pruned: all remain transitively imported or
needed by the recorded lower argument. No module or mathematical obligation is
eliminated from the target closure by this decomposition. The public import SingleComplexBaseChangeStalkCondition was removed from the
new CartesianTensorDataComparison module and moved to a plain proof import of
ProperSupportAffineTensorRestriction, where its additive instance is needed.

For completeness, all old item proof_deps no longer directly used are:
def-weil-pbc-closed-subset-proper-over-base (still needed in its signature),
lem-pc-derived-pullback-perfect (now used by the affine restriction step),
lem-pc-relatively-flat-tensor-base-change-iso (now below cartesian comparison), and
thm-pd-spreading-out (still below noetherian_approximation_data).
lem-pc-noetherian-approximation-data remains directly used.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted two interfaces: preservation of the termwise hypotheses
under tensor pullback, and transport from the canonical base-change square to the
specified cartesian square with descended factor identifications. Neither existing
approximation_data nor the canonical tensor comparison alone states this glue.
The two new obligations isolate precisely those gaps; finite presentation and
proper support were subsequently proved from existing library tools.

The initially missing shared RelativelyFlatTensorBaseChangeIso artifact became
available during work; the intended dependency import was restored and checked.
The local literature/stacks-project/perfect.tex file was absent, so the cited
Stacks sources were read at their official Tag 0A1H, 0A1D and 051D pages. The second reading corrected the new relative-flatness interface and its proof
explanation as described below. No existing statement or target interface changed,
and no forced adaptation was needed.

## New nodes

lem-pc-proper-support-affine-tensor-restriction: a proved construction of the affine
restriction, with its input properties and direct-image comparison. It performs no
Noetherian descent and asserts no direct-image perfectness.

lem-pc-proper-support-tensor-pullback-properties: a proved conjunction of finite
presentation, relative flatness and proper support of a pulled term, using the
separate relative-flatness obligation and existing support/library results.

lem-pc-relatively-flat-module-pullback: the remaining termwise relative-flatness
claim, with no proper support, finite-presentation, complex or derived-image data.
Its stalkwise scalar-extension and localization proof follows Tag 051D,
Lemma 10.100.1(1).

lem-pc-cartesian-tensor-data-comparison: the remaining tensor comparison with
specified factor identifications in an arbitrary cartesian square. It assumes no
Noetherian base, proper support, finite presentation or perfectness. Its proof
uses the existing canonical relatively flat comparison, transport through the
pullback isomorphism, and the given complex and derived-object identifications.

No change records or forced adaptations.

## Second reading by H1

1. Compared all five delivered modules against the repository: four are new;
   the existing properSupport_local_noetherian_model signature and docstring are
   byte-for-byte unchanged. Its only edits are proof imports and proof body.
   No definitions or existing public imports change; no change record is required.
2. Read every proof and both remaining sorry declarations. All five modules compile
   together through lcompile.py. Only relativelyFlat_module_pullback and
   cartesian_tensor_data_comparison contain sorry, each as its entire named public
   theorem proof. No forbidden declaration or hollow definition occurs. The
   delivery axiom probes check every declaration. Independent #print axioms probes
   of all five declarations returned only propext, Classical.choice, Quot.sound
   and sorryAx; sorryAx is expected from the
   two recorded holes and existing open dependencies. Existential witnesses are
   eliminated only inside proposition proofs, never used to define arbitrary data.
3. Read Stacks Tags 0A1H, 0A1D, 051D and 01U4 and the actual IsFlatOver definition.
   Found and repaired a missing quasi-coherence hypothesis in the NEW relative
   flatness lemma: its affine-section conclusion needs the reverse stalk criterion
   of 01U4. Finite presentation at its caller supplies quasi-coherence. Updated
   the new node and expanded the docstring through the final affine-section step.
   The lemma is now the genuine termwise base-change fact, without complex,
   perfectness, support or approximation data. The cartesian comparison has the
   exact qcqs, quasi-coherent E, bounded-above quasi-coherent base-flat G hypotheses
   of 0A1D, and uses ordinary pullback of G. Neither hole restates the item.
   Independently searched with LeanFinder for relative module flatness and arbitrary
   cartesian tensor comparison, Loogle for Module.Flat and TensorProduct, and grep
   for IsFlatOver, isoPullback and complex isomorphisms, plus repository/upstream
   searches. Hits give scheme flatness and ring/complex tools, not either interface.
   Empty schemes, zero modules/complexes and identity base changes are covered.
   Nonflat base changes need only relative module flatness. No new hole can be
   closed in a few minutes from the available interfaces: one needs affine/stalk
   flatness transport and the other derived transport along scheme isomorphisms.
4. Checked the top-down route: affine neighbourhood; canonical tensor restriction;
   explicit finitely generated Z-subalgebra colimit and Noetherian instances;
   existing simultaneous approximation; cartesian comparison; composition of derived
   pullbacks. Finite presentation uses uniqueness of the existing pullback left
   adjoints; proper support uses proved support inverse-image equality, pasted
   pullback, proper base change and independence of closed subscheme structure.
   The unit sk-thm-picard-semicon has realized.statement=[] and steps=[[]]; no fixed
   realization is bypassed. Completed No longer needed with every removed old
   proof_dep. No global module pruning is claimed. Moved
   SingleComplexBaseChangeStalkCondition from a public import of the new cartesian
   module to a proof-only import of the affine step: its additive instance is
   needed for termwise pullback, not for either public statement.
5. Compared node statements, verbatim Lean signatures, proof steps, proof_deps and
   proof_origin to the files. The existing node changes only the permitted proof
   fields. Four new nodes have sources, searches, creation, blueprint, chapter,
   unit and Lean records; the two proved intermediate steps and two remaining
   obligations match the dependency route. Updated the relative-flatness node's
   quasi-coherence hypothesis and stalk-to-sections argument with its Lean.

Second reading changed the new relative-flatness hypothesis and proof explanation,
its node, import visibility/location, and completeness of the pruning report.
No existing statement was changed. Hole accounting remains one old hole closed,
two new holes added (net -1, a decomposition); the two other new steps are proved.
