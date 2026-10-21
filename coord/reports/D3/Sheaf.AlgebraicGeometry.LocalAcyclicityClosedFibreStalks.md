## What changed

Simplified the proved theorem
`AlgebraicGeometry.Etale.closedFibre_derivedUnit_target_stalks` in
`Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks`.
Use the source library's `upperStarCompSheafFiberIso` directly instead of
extracting an isomorphism from `inverseImage_stalk_germ` and discarding its
extra compatibility clause. Replace the private germ-compatibility import by
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.

Use Mathlib's `pullback.map` and `pullback.map_isIso` for the transport between
the small and full strict-local models. Its first-projection equation follows
from `pullback.lift_fst`. This removes the separately constructed inverse and
the two hand-written pullback extensionality proofs. The resulting isomorphism
still transports exactly the same coefficient sheaf.

Update the existing DAG node's proof, proof dependencies and proof origin to
match these changes. The public statement, definitions, public imports and
visibility stay identical. There are no consumer adaptations or interface changes,
so no change record is needed. `tools/downstream.py --uses` found no other live
consumer; the archived `LocalAcyclicityClosedFibreUnit` uses the preserved signature.

## Proved and sorry left

Zero-hole item: 0 existing holes, 0 holes closed, 0 added, 0 split off, 0 left.
The theorem `AlgebraicGeometry.Etale.closedFibre_derivedUnit_target_stalks`
(node `lem-weil-pbc-local-acyclicity-closed-fibre-stalks`) and its existing private
helper `nonempty_cohomology_iso_of_iso_over` have complete proofs.

The original current source compiled before editing. The simplified proof compiled without warnings in 12.5 seconds. Its explicit
`#print axioms` check reported exactly `propext`, `Classical.choice` and
`Quot.sound`. The delivery also runs its standard axiom probe.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` and the item's proof
dependency `lem-weil-pbc-inverse-image-stalk-germ`. The conclusion only asks for
an isomorphism of groups; it does not identify a particular map with germs.
Use the already stated and proved `lemma-openclosed-stalk-upperstar` instead.
The source-library germ-compatibility theorem is preserved unchanged for all
its other users; this delivery does not withdraw any module or declaration.

All remaining imports and mathematical dependencies are used. The explicit
inverse pullback map and its two composite identities are no longer needed,
because Mathlib already proves invertibility of pullback maps along isomorphisms.
No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The repair queue and `coord/rework.tsv` still list the old cluster-restoration
failure, but the current module was restored by M4 (landing
`20261021T225152-L-3785462`) and compiles with zero holes. This delivery therefore
records zero holes honestly and makes an actual proof/dependency simplification,
not a restoration or a claim to close a sorry. The stronger germ-compatibility
node in the old proof dependencies was unnecessary for this existential stalk
comparison. The source argument in Stacks Tag 0GJU requires only preservation
of stalks at this step. The same argument covers q = 0, positive degrees and
empty fibres without further hypotheses.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
