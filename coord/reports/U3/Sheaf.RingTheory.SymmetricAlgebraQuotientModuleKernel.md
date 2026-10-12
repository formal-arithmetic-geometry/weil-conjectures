## What changed

Closed the original theorem directly, using Mathlib symmetric-algebra induction
for surjectivity and the quotient/universal-property argument for the kernel.
The kernel argument adapts the private `SymmetricAlgebra.lift_kernel` proof in
`Sheaf.LinearAlgebra.SymmetricAlgebra.DegreeExact` to independent universes and
the ideal's image-set presentation. Replaced its proof-only DegreeExact import
by the proof-only `Mathlib.LinearAlgebra.Isomorphisms` import. Existing public
imports and the original theorem signature remain unchanged. Removed both new
component theorem modules and their nodes from the proposed delivery.

## Proved and sorry left

Closed: `symmetricAlgebra_quotient_module_kernel` (one original hole).
Added: none. No sorry remains in the delivered module. The previous proposed
`symmetricAlgebra_lift_surjective` and `symmetricAlgebra_lift_ker_eq_span` holes
were removed along with their undelivered modules, not counted as extra closures.
The axiom probe reports only `propext`, `Classical.choice`, `Quot.sound`.

## No longer needed

Removed the proof-only import `Sheaf.LinearAlgebra.SymmetricAlgebra.DegreeExact`
and the old proof dependency `lem-weil-pbc-symmetric-degree-exact` from this node.
This proof no longer reaches that module or its grading dependency; other library
users may still reach them. The proposed SymmetricAlgebraSurjective and
SymmetricAlgebraKernelSpan modules and both new component nodes were withdrawn.

## Where the brief, the DAG or earlier work was wrong

The first proof merely decomposed the conjunction into two unproved clauses,
adding two holes for one closed hole. The target node was still describing
its old degreewise route despite the proposed Lean proof. A direct argument
needs no grading: use Mathlib induction and factor the quotient generator map
through the linear first isomorphism theorem. No arbitrary data is chosen from
an unproved existence theorem; the inverse used here is a proved equivalence.

## Second reading by U3

1. Compared the sandbox module with the repository module using diff. All
   binders, independent universes u/v/w, hypotheses, conclusion, declaration
   name and visibility are byte-for-byte unchanged. No definition or public
   import changed; no change record or forced adaptation is needed.
2. The repaired module compiles locally without errors or warnings. A scratch
   copy with `#print axioms symmetricAlgebra_quotient_module_kernel` prints only
   propext, Classical.choice and Quot.sound. There are no sorry, axiom, unsafe,
   opaque, implemented_by or extern declarations, and no new definitions.
3. Read both proposed split statements and their nodes. They are true strict
   clauses, including for p=id, p:N->0 and the zero ring, but their docstrings
   lacked the full kernel argument and neither was proved. Searched with
   msearch Loogle for SymmetricAlgebra.induction, LeanFinder for determination
   of an algebra homomorphism by generators, and grep for liftQ and the linear
   quotient equivalence; searched Sheaf and upstream Lean for kernel/surjectivity
   declarations. Found the reusable private lift_kernel proof in DegreeExact.
   Removed the split-off statements entirely; there are no new obligations.
4. Induction lifts scalars by f.commutes, generators by hp and lift_ι_apply,
   and sums/products by homomorphism laws. For the kernel, q kills ker p;
   liftQ and quotKerEquivOfSurjective define g with g(p x)=q(iota x).
   algHom_ext verifies lift(g) composed with f equals q, proving ker f <= I.
   Ideal.span_le and p(x)=0 prove I <= ker f. This works with arbitrary
   commutative rings and source/target universes; no finiteness or basis is
   assumed. Imports are used by the signature or the proof. Read
   dag/units/sk-thm-p1.json: neither this node nor the removed degreewise node
   realizes a unit statement or step, so this replacement is below the unit
   level and all realized nodes and the unit route are preserved.
5. Replaced the item's proof plan with the two actual Mathlib arguments,
   set proof_deps to empty (no project theorem is called), and recorded the
   proof's origin including the private kernel proof adapted. Removed the two
   proposed new nodes, whose metadata was incomplete and whose dependencies
   were not used by the actual code. Node statement and lean record are unchanged.

Second reading changed the proof from a two-hole decomposition to a complete
proof, removed both split modules/nodes, updated the theorem's proof docstring,
corrected the proof plan and dependencies, and rewrote this report.
