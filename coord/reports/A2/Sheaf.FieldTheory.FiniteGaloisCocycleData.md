## What changed

Proved `Field.exists_finite_galois_cocycle_data` in
`lean/Sheaf/FieldTheory/FiniteGaloisCocycleData.lean`, preserving its signature,
visibility, and existing docstrings. Added two proved private helpers:
`Field.finite_pair_factorization` and `Field.scalar_cocycle_identity`.

The factorization applies the existing open-normal-stabilizer theorem to the
product group, intersects the coordinate pullbacks, constructs its finite quotient,
and transports the quotient group law to `Fin n`. Representatives are selected from
the proved surjectivity of this explicitly constructed quotient homomorphism.
The identity is derived directly from the homogeneous differential and equivariance,
then transported to every quotient index using surjectivity. Continuity is proved
with compact-open evaluation on the locally compact absolute Galois group.

Added proof-only imports `Sheaf.Topology.ContinuousOpenNormalStabilizer`,
`Mathlib.FieldTheory.Galois.Profinite`, and `Mathlib.Tactic.Abel`. Updated
`lem-sc-finite-galois-cocycle-data`'s proof and proof dependencies to match.
No definitions, public signatures, or target statements changed.

## Proved and sorry left

Closed the one original hole: `Field.exists_finite_galois_cocycle_data`
(node `lem-sc-finite-galois-cocycle-data`). Both new private helpers are proved.
There are no remaining sorries in the delivered module and no new sorries anywhere
in this delivery: one hole closed, zero holes added, zero statements split off.

The proof uses the existing stated theorem
`ProfiniteGrp.exists_openNormalSubgroup_right_invariant`
(node `lem-exc-coinduced-functions-open-stabilizer`, module
`Sheaf.Topology.ContinuousOpenNormalStabilizer`), which still has its own sorry.
Thus this is a stage-3 proof from an existing dependency; it does not claim an
axiom-free proof of the entire import closure.

## No longer needed

No original imports, nodes, or modules were pruned. The original module had only
its statement dependency import and its node had no named proof dependencies.
The finite clopen-rectangle and normal-core construction planned inside this node
is handled by the existing product-group stabilizer theorem; no new nodes for
those steps are needed. A trial import of `Mathlib.Algebra.Group.TransferInstance`
was removed after Lean confirmed its declarations were already available.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The plan omitted the existing
open-normal-stabilizer node, which supplies its compactness step on the product
group. The transported group law on `Fin n` must be installed explicitly, including
its multiplication instance; the proof does so and never uses modular multiplication.
The homogeneous cocycle need not be normalized, and the proof does not assume
that its value at the identity is one. Trivial groups and constant cocycles are
covered by the same quotient construction. The unit `sk-thm-br` has no realization
attached to this node, and its recorded route is unchanged.

## Second reading by A2

1. **Interface and accidental changes.** I diffed the delivered module against the
repository version. The existing public declaration and all definitions retain their
signatures byte-for-byte; only proof-only imports, private helpers, and the target
proof changed. The node now records the stabilizer theorem actually used.

2. **Proof and axioms.** `lcompile.py` compiles the module without errors or warnings.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`
tokens in the delivered files. The target's axiom print contains only the allowed
kernel axioms plus `sorryAx` inherited from the explicitly imported open-stabilizer
theorem, which is documented as an existing dependency.

3. **Statements and searches.** The target statement is unchanged and the two
private helpers are proof-local, with no new public statements or split-off holes.
The recorded Mathlib and library searches were checked; no existing declaration
matching either helper was found. The factorization handles the nonempty and
trivial-quotient cases, and the cocycle calculation assumes no normalization.

4. **Pruning and route.** The added imports are all used: the open-normal-stabilizer
module supplies the stated proof dependency, `Galois.Profinite` supplies profinite
instances, and `Abel` closes the additive rearrangement. No old import or node is
unused, and the `sk-thm-br` unit record and route remain unchanged.

5. **Node agreement.** The helper proof follows the node's finite quotient and
homogeneous differential steps, and the node's `proof`, `proof_deps`, and
`proof_origin` now agree with the Lean proof. No new nodes or change records are
needed. I changed only this report and the delivered proof/node metadata as described
above.

The module compiles locally without errors or warnings through `lcompile.py`.
