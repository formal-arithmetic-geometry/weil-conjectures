## What changed

Proved `AlgebraicGeometry.Scheme.Modules.closedImmersion_pushforward_annihilated`
with its original signature and visibility. The only Lean file delivered is
`lean/Sheaf/AlgebraicGeometry/ClosedImmersionPushforwardAnnihilated.lean`.

Pushforward quasi-coherence follows from `affinePushforward_baseChange` on the identity
base-change square. Sectionwise annihilation is proved directly: membership in the ideal
kills the section under the subscheme inclusion, and the scheme-theoretic-image factorization
then kills it under `i.app V`. Restriction of scalars makes its action zero.

Pullback quasi-coherence is transferred from the proved Mathlib-compatible pullback instance
using uniqueness of left adjoints. For the unit, the existing `closedImmersion_unit_quotient`
lemma provides an epi with kernel the image of ideal multiplication. Tensor induction and
the sheafification adjunction prove that annihilation makes that multiplication zero;
its image inclusion is consequently zero. The kernel universal property makes the unit mono,
so it is an isomorphism. The two choices of adjunction are compared explicitly, proving
invertibility of precisely the unit in the original statement. Finite type follows directly
from `tensorPullback_isFiniteType`.

The original DAG node's proof, proof dependencies, and proof origin now describe this route.
No statements, definitions, public imports, or other modules were changed. New proof imports
are `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`,
`Sheaf.AlgebraicGeometry.ModulePullbackFiniteType`, and
`WeilConjectures.AlgebraicGeometry.Modules.TensorSection`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.closedImmersion_pushforward_annihilated`.
There are no remaining `sorry`s in the delivered module and no new holes or declarations.
This is a proof from existing stated dependencies, not a decomposition into new statements.
It still uses the existing holed declarations `affinePushforward_baseChange`,
`closedImmersion_unit_quotient`, and `tensorPullback_isFiniteType`; these were not changed.

The module compiles cleanly using the prescribed local compiler. The proof covers empty
schemes, the identity immersion, and the zero module: no nonemptiness, nonzero, finite type,
or extra coherence hypothesis is used for the unit argument. The finite type hypothesis
is used only in the final conditional clause.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`.
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`.
- `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`.
- `Sheaf.AlgebraicGeometry.TensorPullback` (already supplied by the statement imports).
- `Sheaf.Topology.PresheafModuleStalkFunctor`.

Removed direct DAG proof dependencies: `lem-weil-pbc-closed-immersion-finite`,
`lem-weil-pbc-support-pullback-finite-type`, `lem-weil-pbc-module-iso-on-stalks`,
`lem-weil-pbc-closed-pushforward-stalks`, `def-weil-pbc-module-stalk`,
`lem-weil-pbc-locally-surjective-iff-stalks`, and `lem-weil-pbc-module-stalk-pullback`.
The stalk and tensor-pullback tools remain needed transitively by the unit/quotient lemma;
this delivery does not claim to prune them from the whole targets' import closure.
The larger support theorem is replaced by the smaller finite-type pullback theorem.
No unit-level statement or realized step is bypassed: this node is below the unit's realized
statements and the unit/quotient lemma and finite-type pullback lemma are in the same unit.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The direct stalk plan is unnecessary in
this module because the already stated unit/quotient theorem packages that calculation.
The original theorem docstring remains the source's stalkwise explanation; the proof-body
comment and updated DAG record explain how it is now invoked through the unit/quotient lemma.

Searches: LeanFinder found open-immersion restriction and adjunction results but no closed
immersion unit theorem; Loogle returned no hits for closed immersion plus module pushforward.
LeanSearch was unavailable (HTTP internal server error). Source searches found no direct
proof of this theorem, but identified the existing unit/quotient interface and the proved
TensorSection and pullback-quasi-coherence tools. The source proof was read in the local
Stacks copy at `/home/ubuntu/work-bp/sheaf/literature/stacks-project/modules.tex`,
Lemma 08KS, and `morphisms.tex`, Lemma 01QY.

## Second reading by X3

1. **Interface: PASS.** Read the complete repository/sandbox diff. The existing theorem
   signature is byte for byte unchanged; all public imports and visibility are unchanged.
   There are no definitions, extra declarations, or change records in this delivery.
2. **Proof: PASS.** Independently compiled the module without errors or warnings. A scratch
   copy with `#print axioms AlgebraicGeometry.Scheme.Modules.closedImmersion_pushforward_annihilated`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected
   from the existing open dependencies. Scanned the delivered code for forbidden constructs
   and holes: none. Read the sectionwise tensor calculation, zero-image kernel argument,
   and comparison of the two adjunction units; each proves the stated conclusion. No data
   is extracted from an arbitrary unproved existence statement: adjunction choices are
   compared by the uniqueness isomorphism with precisely the equality used downstream.
3. **Split statements: PASS (none).** No new statements or holes were split off. The
   existing quotient theorem is a genuinely stronger general quotient calculation, not
   a renamed copy of this item. Identity immersions, empty schemes and zero modules cause
   no exception; the zero-kernel argument requires no extra finiteness hypothesis.
4. **Route and pruning: PASS.** Read `dag/units/sk-thm-p1.json`: this item is not a realized
   unit statement or step, and every realized route remains intact. Independently searched
   Mathlib/upstream module sources for annihilation, kernel scalar action and unit
   isomorphisms; a fresh LeanFinder query about modules killed by a closed-subspace ideal
   found only open-immersion tools and the closed-immersion/ideal-sheaf equivalence, not
   a shorter module theorem. The retained Tilde proof import supplies the proved
   `isQuasicoherent_pullback` instance; TensorSection supplies the pure-tensor formulas;
   the other proof imports supply the three invoked stated theorems. All seven old
   proof dependencies removed from the new route are listed under `No longer needed`.
   The old stalk tools remain transitively imported by the quotient theorem, as reported.
5. **DAG: PASS after repair.** Only `proof`, `proof_deps`, and `proof_origin` differ from
   the repository node. The dependency list equals the union of the proof steps' uses.
   Added the previously omitted `lem-pc-module-pullback-adjunction` dependency to the
   left-adjoint comparison steps, since the proof invokes its proved
   `exists_tensorPullbackAdjunction` declaration explicitly.

Second-reading changes: updated the theorem's proof docstring to describe the actual
quotient/zero-kernel route rather than the obsolete direct stalk argument; added the
missing adjunction dependency in the DAG; removed trailing whitespace. The Lean proof
itself was correct and was preserved. One original hole closed, zero holes added,
zero split-off statements. No claim of complete axiom-free target closure is made.
