## What changed

Replaced the original worker's pairing of two clause-restatements with a genuine
reduction in `ExternalCupUnitCoefficientIdentities`. Unfold externalCup, factor the
coefficient map through the tensor coefficient map, apply the existing
`scalarCup_coefficient_naturality`, identify the pulled-back class of one, and use
the cup-unit identities on the product scheme. No existing signature or definition
changed. All added imports in the item are proof-only.

Added `ScalarCupUnitIdentities` and `ScalarUnitClassPullback`; removed the undelivered
`ExternalCupUnitCoefficientLeftIdentity` and `ExternalCupUnitCoefficientRightIdentity`
modules and nodes. The replacement obligations concern respectively one scheme with
no projection and degree-zero pullback with no cup product. Neither restates a clause
of the original external-product theorem. Updated the original node's proof,
proof_deps and proof_origin to describe the actual Lean reduction.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.Scheme.Modules.external_cup_unit_coefficient_identities` (one of
one original holes). The item's module has no remaining sorry.

Added two holes:

- `AlgebraicGeometry.Scheme.Modules.scalar_cup_unit_identities`, node
  `lem-sc-scalar-cup-unit-identities` in `ScalarCupUnitIdentities`.
- `AlgebraicGeometry.Scheme.Modules.scalar_unit_class_pullback`, node
  `lem-sc-scalar-unit-class-pullback` in `ScalarUnitClassPullback`.

This is a decomposition, not a completed axiom-free proof: one hole closed, two
added, net minus one before the maintainer measures changes in the import closure.
The existing coefficient-naturality theorem and other upstream dependencies remain
open. The two discarded worker holes were never landed and are not counted as
closed holes. Explicit #print axioms checks on all three delivered theorems show
only propext, Classical.choice, Quot.sound and sorryAx. Each new hole is exactly
`:= by sorry`, with a source, complete proof docstring and matching node.

## No longer needed

Removed proof-only import `Sheaf.Paper.ModuleCohomologyCupProduct`, corresponding to
old proof dependency `def-sc-module-cohomology-cup-product`. The actual reduction
uses Ext-defined scalar operations and coefficient naturality, without invoking
that module's acyclic-resolution characterization. Every other old proof dependency
is retained: scalar-unit coordinates supplies the explicit class definition, the
scalar operations supply externalCup and the coefficient maps, and tensor pullback
of the structure sheaf supplies the adjoint maps.

Withdrew the two undelivered clause-restatement modules and nodes named above.
No claim is made that removing one import globally prunes an entire library module.

## Where the brief, the DAG or earlier work was wrong

The first worker's two new statements were exactly the two conjuncts of the item,
and their pairing did not carry out the intended mathematical argument. The old
node was not updated to match even that proof. Their lean.statement fields also
contained "see Lean declaration" rather than the required verbatim signatures.
The replacement makes the geometric reduction explicit and gives verbatim records
for genuinely separate unit calculations. There was no mathematical error in the
original statement and no statement correction is needed.

## New nodes

`lem-sc-scalar-cup-unit-identities`: the two unit actions on structure-sheaf H1 on a
single scheme. Its proof follows the Ext description of cup in Stacks Tag 0FKU,
Lemma 20.31.1, evaluation at one, and unitor naturality. The left and right unitors
agree at the tensor unit, explaining the use of the same displayed coefficient map.

`lem-sc-scalar-unit-class-pullback`: degree-zero pullback of the canonical unit class
followed by the adjoint structure-sheaf map preserves one. Its proof uses Tag 01F7
and the normalized pullback adjunction (Tags 0096 and 01CA). The ring map preserves
one, including when the destination is empty. There are no change records because
no existing statement or definition is altered.

Both nodes keep the item's chapter, unit and blueprint ancestry. New searches used
queries about cup with the section one and inverse image of its degree-zero class,
not the original worker's external-product query. LeanFinder returned group and
nonabelian cohomology results only. LeanSearch returned Internal Server Error and
is recorded as unavailable. Grep of Mathlib Ext and sheaf cohomology, the upstream
module sources, and lean/Sheaf found Ext composition/transport infrastructure but
no existing declaration of either replacement obligation.

## Second reading by A3

1. Compared the delivered item with the repository using diff and an exact signature
   comparison. Verdict: the theorem signature, original local instance, public
   imports, and all definitions are unchanged byte for byte; only the proof and
   proof-only imports differ. No target or downstream interface is changed.

2. Compiled all three modules locally with lcompile.py in import order, without
   errors or warnings. Explicit axiom probes for the three theorems found only the
   standard axioms and sorryAx. Scanned the sources: no axiom, unsafe, opaque,
   implemented_by, extern or definition containing sorry. Verdict: a correct Lean
   reduction with exactly the two named open statements reported above.

3. Read the statements and natural-language proofs of both replacement obligations.
   The cup-unit statement has one base scheme and no geometric pullback; the
   pullback statement has degree zero and no tensor cup operation. Checked zero
   degree-one classes, the empty scheme (zero sections), affine schemes (H1=0),
   identity pullback, and field characteristic two: there is no sign or additional
   assumption in these cases. Left/right unitors agree on O tensor O. Searched
   Mathlib, the upstream module library and lean/Sheaf using the queries recorded
   above. Verdict: true, needed, strictly separate parts of the argument, with no
   existing duplicate found. Neither could be closed in a few minutes because both
   still require the injective-resolution comparison with the canonical class of
   one, which has no existing exported degree-zero lemma here.

4. Read Stacks Tags 0BED (the external product definition preceding the Kunneth
   calculation), 0FKU (especially Lemma 20.31.1), and 01F7 via their online pages;
   the sandbox does not have the node's referenced literature checkout. The proof
   uses the external-product definition, not Kunneth assumptions. Checked the
   unit `dag/units/sk-prop-av-cube.json`: its realized statement and step lists are
   empty, and no unit-level route is bypassed or edited. Pruning is below that
   level. Verdict: a shorter genuine reduction; unused acyclic-resolution import
   and its old proof dependency are reported completely.

5. Opened all delivered nodes and compared their Lean signatures with their
   lean.statement records. The original node's two steps now follow map composition,
   coefficient naturality, preservation of one and the single-scheme unit actions;
   proof_deps is the union of the steps' uses. New records have source, searches,
   proof, origin, ancestry, creation metadata and verbatim Lean records. Verdict:
   the DAG agrees with the Lean; the original statement and stmt_deps are unchanged.

Changed on second reading: removed both clause-restatement modules/nodes; supplied
an actual reduction and two different unit obligations; removed the unused cup
characterization import; corrected the proof metadata and report. The final delivery
is a decomposition and explicitly reports the two remaining holes.
