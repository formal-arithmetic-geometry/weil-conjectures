## What changed
Proved `AlgebraicGeometry.Scheme.Modules.unitCohomologyPullbackLinear_bijective`
by the original two-component argument: the inverse-image action on Ext is
bijective, and the adjoint coefficient morphism is an isomorphism. Added the single
plain proof import `Mathlib.CategoryTheory.Sites.Equivalence`. The explicit linear-map definition and the existing theorem
signature are unchanged.

## Proved and sorry left
Closed the original hole `unitCohomologyPullbackLinear_bijective` (one of one).
Added no holes. Removed the first worker's proposed
`unitCohomologyPullbackLinear_inverse` and its new node: this existential
set-theoretic inverse was equivalent to the original bijectivity assertion,
not a strictly simpler part of the argument. This delivery is a proof, not a
decomposition.

## No longer needed
No old proof dependencies or modules were pruned: the only original dependency,
`def-pbc-unit-cohomology-pullback-linear`, remains used. The proposed new
`new-lem-pbc-unit-cohomology-pullback-linear-inverse` node is withdrawn before
landing.

## Where the brief, the DAG or earlier work was wrong
The original DAG's equivalence-and-coefficient route was sufficient. The first
worker's assertion that an existential inverse was a strict lower decomposition
was wrong: existence of a two-sided set-theoretic inverse is equivalent to
bijectivity under classical choice. No lower statement was necessary.

## Second reading by C3
1. Compared the sole delivered module against the repository with `diff`.
   Both existing declaration signatures and the entire definition are unchanged;
   only the theorem proof and plain proof imports changed. No interface change
   or change record is needed.
2. Read the full proof: it constructs the equivalence of opens from the given
   scheme isomorphism, transfers it to abelian sheaves, and composes the two
   bijections. The coefficient is an actual adjunction image of the specified
   morphism; no data is chosen from an unproved existence statement. Local
   compilation and axiom checks are recorded below.
3. Rejected and removed the proposed inverse-identity split and its node.
   No split-off theorem remains. Repeated searches with Loogle
   (`CategoryTheory.Equivalence.sheafCongr`), Lean Finder (exact fully faithful
   functors and Ext bijections), and `rg` in the library and Mathlib found the
   generic APIs used in the proof, not a duplicate of the specific comparison.
   The proof requires no nonempty scheme, nonzero ring, or positive degree:
   identity isomorphisms, empty schemes, zero rings, and degree zero all fall
   under the same categorical argument.
4. The original shortest two-component proof route is retained. Imports used
   only for the proof are plain imports. No original proof dependency is unused.
   `dag/units/sk-thm-p1.json` was read: this supporting node does not replace
   any unit-level statement or realized step, and the unit route is untouched.
5. Updated the existing theorem node's `proof` and `proof_origin` to describe
   the actual dense-subsite equivalence, componentwise coefficient isomorphism,
   adjunction counit, and composite cohomology bijection. Its `proof_deps`
   remains the union of the steps' dependencies. No new node is delivered.

Second reading changed: removed the equivalent restatement and proved the
original theorem directly; replaced the report and aligned the original DAG node.

Validation: the final scratch copy compiled in 59.0 seconds with no warnings.
`#print axioms` for both `unitCohomologyPullbackLinear` and
`unitCohomologyPullbackLinear_bijective` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivery dry run
printed `OK`: compilation, the all-declaration axiom probe, and preflight passed.
Definition and signature byte comparisons and the 100-character line check passed.
