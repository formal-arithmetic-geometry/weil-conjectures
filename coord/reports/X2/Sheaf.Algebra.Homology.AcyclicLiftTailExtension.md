## What changed

Proved `CochainComplex.exists_extend_acyclicLiftTail` with its original signature and
`AcyclicLiftTail` definition unchanged. Its proof chooses the next term, lifts its differential,
splices it into the old complex, and checks all support, term-class, exactness and comparison
conditions. Added proof-only imports of `AcyclicLiftNextDifferential`,
`SpliceIncomingDifferential`, `Mathlib.Algebra.Category.ModuleCat.Abelian`, and
`Mathlib.CategoryTheory.Adjunction.Additive`.

Added three fully proved intermediate modules:

- `Sheaf.Algebra.Homology.AcyclicLiftSplitCycles`: downward induction gives membership of
  cycles in P, splits consecutive cycle sequences, and proves that reduction preserves the
  required monic kernel sequence.
- `Sheaf.Algebra.Homology.AcyclicLiftNextDifferential`: uses that kernel sequence and acyclicity
  to construct a surjection on reduced cycles. Mathlib tensor surjectivity proves surjectivity of the
  quotient adjunction unit. Projectivity lifts the map through this unit, the hypothesis
  upgrades reduced surjectivity to surjectivity, and composition with the cycle inclusion
  supplies the desired differential.
- `Sheaf.Algebra.Homology.SpliceIncomingDifferential`: explicitly constructs the modified
  complex and both chain maps. Component formulas prove their isomorphism and comparison
  properties; short-complex isomorphisms transfer exactness.

Updated the original node's proof route and added nodes for the three intermediate statements.
All helper imports are proof-only. No interface changes or forced adaptations were needed.
The proof follows [Stacks Tag 0BC9](https://stacks.math.columbia.edu/tag/0BC9), first two proof
paragraphs, and retains the unit's route. All four files compile without warnings in approximately
3–5 seconds each.

## Proved and sorry left

Closed the sole original hole, `CochainComplex.exists_extend_acyclicLiftTail`
(`lem-sc-acyclic-lift-tail-extension`). No sorries remain in the item, and no sorries were added.
This is a complete proof, not a decomposition into unproved statements.

Also proved `CochainComplex.exists_acyclicLift_splitCycles`
(`lem-sc-acyclic-lift-split-cycles`), `CochainComplex.exists_acyclicLift_nextDifferential`
(`lem-sc-acyclic-lift-next-differential`), and
`CochainComplex.exists_spliceIncomingDifferential` (`lem-sc-splice-incoming-differential`).
The private `quotient_unit_surjective` helper uses Mathlib `TensorProduct.mk_surjective`
and `Ideal.Quotient.mk_surjective` after the second reading.
All dependencies of these proofs are Mathlib declarations or these fully proved new modules.

The arguments cover the empty tail n=b+1, the zero complex, the zero ring, and the zero or unit
ideal. The splitting lemma even allows n>b. The support check uses n<=b+1 precisely to keep the
new degree n-1 below the old upper bound. There is no finite-generation assumption.

## No longer needed

None. The original node had no proof dependencies or proof-only imports to prune. All original
public imports remain because they supply the existing statements and structure; all added
proof-only imports participate in the completed proofs. The existing bounded-projective model
lemma was inspected for its descent argument but is not imported: it does not give membership
in the arbitrary class P or the required reduction comparison. No DAG node or library module
is made unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The original DAG had no named dependencies for its three non-elementary proof steps. The three
new nodes now record those steps, with complete proofs. The copied source path
`literature/stacks-project/more-algebra.tex` is absent on this machine; the cited proof was read
from the official Stacks page instead. LeanSearch returned HTTP Internal Server Error and is
recorded as unavailable; LeanFinder, Loogle and source searches worked. No mathematical error,
statement dispute, or change to the unit route was found.

## New nodes

`lem-sc-acyclic-lift-split-cycles`, in
`dag/nodes/sec-abelian-varieties/lem-sc-acyclic-lift-split-cycles.json`, records the finite-tail
splitting and reduction argument. Its module and theorem are fully proved.

`lem-sc-acyclic-lift-next-differential`, in
`dag/nodes/sec-abelian-varieties/lem-sc-acyclic-lift-next-differential.json`, records the
projective lifting and surjectivity argument. Its sole proof dependency is the split-cycle node,
and its module and theorem are fully proved.

`lem-sc-splice-incoming-differential`, in
`dag/nodes/sec-abelian-varieties/lem-sc-splice-incoming-differential.json`, records the explicit
generic cochain-complex splice with an additive comparison functor. Its module and theorem are
fully proved. No change record is required.

## Second reading by X2

1. I compared the delivered target module with the repository version. The `AcyclicLiftTail`
structure and `exists_extend_acyclicLiftTail` signature are unchanged byte for byte; only
proof-only imports and the proof body were added. The three new helper modules are new files,
and no existing declaration outside this item was adapted.

2. I compiled all four delivered modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all`.
They compile without errors or warnings. A source scan found no `sorry`, `axiom`, `unsafe`,
`opaque`, `implemented_by`, `extern`, or `sorryAx`. The delivery axiom probe passed for every declaration. Scratch `#print axioms` checks
for the target, next-differential and splice theorems returned exactly `propext`,
`Classical.choice`, and `Quot.sound`.

3. I checked the helper statements against their proofs and the Stacks Project Tag 0BC9
argument. Split-cycle membership and reduced kernel exactness, lifting the next differential
through the reduced cycles, and the explicit incoming splice are each proper intermediate
claims, strictly smaller than the target and needed by the target proof. Their edge cases
(empty tail, zero terms, and n=b+1) are handled by the integer support branches in the proofs.
Searches found no existing declaration with any of these statements.

4. The target proof follows the stated route: choose the supplied lift, construct the next
differential, splice it, and assemble the new tail. The unit route is retained. Existing
public imports remain statement dependencies; the newly added imports are all used by proofs
and are private imports. No unused node or import was found to prune.

5. The DAG records for the target and the three helper nodes match the Lean theorem names,
signatures, proof steps, dependencies, source, and unit. The target closes its original hole,
and the delivery adds no sorry holes or definitions. No statement or definition change record
is required.

I replaced the private tensor-induction proof of `quotient_unit_surjective` with
`TensorProduct.mk_surjective`, adding its proof-only Mathlib import. The helper statement
and all public signatures are unchanged. I updated its DAG proof step and the report
to record the shorter route. No other proof or DAG content required repair.
