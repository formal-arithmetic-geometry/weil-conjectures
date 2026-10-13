## What changed

Proved `ModuleCat.tensorAugmentation_quasiIso_of_torIndependent`, preserving its
signature and existing public imports. Added three proof imports: the new scalar
augmentation module, `MixedTensorRestrictionComparison`, and the upstream homotopy
category braiding module.

Added `Sheaf.Algebra.Homology.TorIndependentScalarAugmentation`, whose public theorem
`ModuleCat.scalarAugmentation_quasiIso_of_torIndependent` is proved. It applies the
existing single-support Tor lemma to a K-flat resolution of A[0]. In the tensor square
with F -> B[0], three sides are quasi-isomorphisms, and two-out-of-three proves the
fourth. Natural single-factor comparisons identify it with scalar extension.
The identity R-linear equivalence on B handles the distinction between its
algebra module structure and its module structure obtained by restriction;
the analogous comparison for A identifies restricted scalar extension with tensoring by A.

The main module proves a private general helper converting the acyclic-tensor
hypothesis to K-flatness. It tensors the scalar-extended map over A, uses the signed
flip and the natural mixed tensor restriction comparison, and finally braids the
R-tensor factors. This is the arbitrary unbounded Q part of the argument.

Updated the item's DAG proof and added a node for the proved scalar calculation.
The unit record has no realized statement or proof steps here; the change stays
below the unit level. No definitions or existing signatures changed.

## Proved and sorry left

Closed the sole original hole:
`ModuleCat.tensorAugmentation_quasiIso_of_torIndependent`
(node `lem-pc-tor-independent-tensor-augmentation`).

Also proved the new public helper
`ModuleCat.scalarAugmentation_quasiIso_of_torIndependent`
(node `lem-pc-tor-independent-scalar-augmentation`) and the private helper
`ModuleCat.tensor_restricted_quasiIso_of_scalarExtension`.

There are no sorries in either delivered module and no new holes. This is a proof
from existing stated dependencies, not a decomposition into new holes. It still
rests on the existing imported theorem
`CochainComplex.quasiIso_tensor_of_single_support_tor_acyclic`
(node `lem-pc-single-support-tor-acyclic-tensor`, module
`Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor`), which currently has sorry.
No claim of a sorry-free transitive proof is made.

## No longer needed

No existing import was removed: the original five are public statement imports,
and all three new proof imports are used.

The item's proof no longer needs `lem-pc-kflat-derived-tensor-associator` or its
module `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator`. The proof uses the
explicit mixed tensor restriction comparison instead of a derived trifunctor
associator. This is pruning of this proof branch, not a claim that other targets
have stopped using that module.

The old direct proof dependencies `lem-pc-module-bounded-flat-kflat` and
`lem-pc-mixed-tensor-kflat-quasi-iso` are no longer direct dependencies of this item;
they remain dependencies of the existing single-support Tor lemma used by the
scalar helper, so they are not pruned from the transitive argument.
`def-weil-pbc-tor-modules` remains a statement dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped because no existing declaration immediately matched
the unbounded augmentation. That missed the tensor-square reduction: resolve A[0],
apply the existing one-term Tor lemma to this resolution with B, and use K-flatness
of F on the other side of the square. This avoids both balanced Tor computed by
resolving B and a common-refinement construction in the present delivery.

The search used LeanFinder (eight flat-module exactness hits), Loogle (unqualified
Tor was not recognized), and grep (Mathlib Tor.lean has no balancing theorem).
LeanSearch returned Internal Server Error. The library search located the existing
one-term theorem and the natural mixed tensor restriction comparison.

Checked the source at Stacks Tags 06Y6 and 08IB online. The new helper expresses
only the scalar Tor calculation; it has no arbitrary Q and no Q-flatness assumption.
Its proof uses the same coefficient universe and the exact Tor' ordering A,B.
The tensor square applies equally to unbounded F, zero rings and zero modules;
no nonzero, boundedness, or flatness-of-A hypothesis was introduced.

## New nodes

`lem-pc-tor-independent-scalar-augmentation` in
`dag/nodes/sec-picard-framework/lem-pc-tor-independent-scalar-augmentation.json`
records the proved scalar-extension augmentation theorem, in the new module
`Sheaf.Algebra.Homology.TorIndependentScalarAugmentation`. Its proof depends on the
existing one-term Tor calculation and K-flatness. No change record is needed:
all existing signatures, definitions and public imports are unchanged.

## Second reading by H4

1. Compared both delivered modules with the repository. The scalar module is new;
   the existing augmentation theorem's signature is byte-for-byte identical.
   All five existing public imports remain. No definition or target statement
   changes, and no change record or forced adaptation is needed. PASS.
2. Read both proofs and checked for forbidden declarations and holes: neither
   delivered file contains `sorry`, an axiom, unsafe code or hollow data.
   The resolution is obtained from the proved functorial-flat-resolution instance,
   whose construction uses copowers of a flat separator, not unproved existence.
   The scalar calculation uses the existing open single-support theorem; the
   arbitrary-Q comparison itself uses proved K-flatness and natural isomorphisms.
   Local compilation and explicit axiom checks are recorded below.
3. No statement is split off with `sorry`. The proved new scalar lemma is strictly
   the scalar calculation, without Q or its acyclic-tensor hypothesis. Checked
   its tensor-square proof, the Tor argument order A,B, restriction of algebra
   module structures, unbounded F, zero rings and zero modules. No additional
   flatness or nonzero assumption is needed. Repeated searches with different
   words through LeanFinder, Loogle and grep; no shorter matching result appeared.
   The existing `scalarExtension_quasiIso_of_torIndependent_kFlat` uses this item
   and cannot be used here without a circular import. PASS.
4. Reviewed from the augmentation downward: the one-term Tor lemma computes the
   scalar augmentation, then the K-flatness of Q and the explicit mixed-tensor
   comparison finish the proof. All added proof imports are plain imports;
   the public imports supply the statement's coefficient categories, Tor and
   K-flatness infrastructure. The No longer needed section accounts for every
   old direct proof dependency; the Tor definition remains a statement dependency.
   The unit's `realized` statement and step lists are empty, so no realized unit
   step is bypassed. Checked Stacks Tags 06Y6 and 08IB against this route. PASS.
5. Read both node records against the Lean. Their proof steps, dependency unions
   and proof origins match the scalar tensor square and mixed restriction proof.
   The new node has its source, search records, creation, blueprint, chapter,
   unit and verbatim Lean statement. Existing-node edits are confined to the
   stage-3-owned proof fields. PASS.

Changed the existing theorem's outdated proof docstring to describe the actual
scalar tensor-square and mixed-restriction argument. No proof term, signature,
definition or import needed repair.

Verification: each delivered module compiled locally without warnings. Explicit
`#print axioms` on a scratch copy reported only `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx` for the two public augmentation theorems; the private
restricted-tensor helper uses only the three allowed axioms. The `sorryAx` is
consistent with the existing open single-support Tor comparison, not a new hole.
