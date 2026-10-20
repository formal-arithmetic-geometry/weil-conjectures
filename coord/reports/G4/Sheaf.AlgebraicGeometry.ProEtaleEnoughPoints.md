## What changed

Proved `AlgebraicGeometry.proEtale_enoughPoints` with its signature unchanged.
The proof applies the existing affine-subsite equivalence and finitary-slice
criterion. Four proved private helpers supply closure under affine pullbacks,
the affine site's covering axioms, finite refinements in slices, and the epi
from all sheafified representables to the terminal sheaf. The points are
transported by composing geometric morphisms; the equivalence reflects isomorphisms.

Added the private proof import `Mathlib.CategoryTheory.Limits.FullSubcategory`.
A local priority for the direct sheaf-colimit instance avoids an expensive
search through general full-subcategory closure instances. Updated the node's
proof to match the Lean implementation and removed its ring-stability dependency.
The proof-context commands are documented in
`coord/changes/G4-proetale-enough-points-proof-context.md`; no consumer is adapted.

Validation: the complete item compiled on the project server in 1.9 seconds,
without errors or warnings. Finite refinements use presieve support rather than
assuming that an indexed presentation of a finite presieve has finite index type.
Empty support, repeated arrows, an empty scheme, and arbitrary non-affine or
non-quasi-compact bases require no extra hypotheses.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.proEtale_enoughPoints`
(node `lem-sfb-proetale-enough-points`). All four private helper proofs are complete.
The item has zero remaining `sorry`; the delivery adds zero holes and splits off
zero statements. This is a proof from existing declarations, not a decomposition.

The proof uses the already stated downstream theorems
`AlgebraicGeometry.Scheme.ProEt.affineWeaklyEtale_sheafEquivalence`
(node `lem-sfb-proetale-affine-subsite-equivalence`) and
`CategoryTheory.finitarySlice_enoughPoints`
(node `lem-sfb-site-finitary-slice-enough-points`). Their existing holes remain
outside this item and are not changed or duplicated by this delivery.

## No longer needed

Removed `import Sheaf.RingTheory.IndEtaleStability` and removed
`lem-weil-pbc-ind-etale-stability` from this node's proof dependencies and
maintainer-approved tool list. The native Mathlib weakly-etale small-site
finite-limit and preservation instances provide the needed stability directly;
no ring-level ind-etale or principal-Zariski argument is used here.
This does not assert that the module is unnecessary to other library consumers.
All other planned mathematical inputs remain in the route. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned affine geometry did not require reproving weakly-etale stability at
ring level: Mathlib already implements the small-site limits and their preservation.
The phrase that a finite covering family refines itself needs care for the actual
Lean interface, which quantifies over arbitrary presentations, including infinite
repetitions. Selecting from the finite arrow support gives the required finite
indexed refinement with identity refinement maps.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
