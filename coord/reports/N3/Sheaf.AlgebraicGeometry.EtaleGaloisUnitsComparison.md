## What changed

Completed the assigned retirement from coord/retire-items.tsv. Withdraw
Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison using deleted.txt and repoint
lem-sc-etale-galois-units-comparison to the existing source construction
AlgebraicGeometry.Scheme.cohomologicalBrauerGroupAddEquivGaloisUnitsH2 in
WeilConjectures.AlgebraicGeometry.EtaleGaloisUnitsComparison. Its inverse type
equivalence proves the exact former theorem. The mathematical node statement,
its hypotheses and the unit route are unchanged.

Updated the node proof fields to the source's direct stalk-cohomology comparison.
The source construction and its stalk/equivariance arguments were read in full.
The exact former theorem compiled from `.symm.toEquiv` in 4.3 seconds, and
`#print axioms` for both declarations returned only propext, Classical.choice and
Quot.sound. The check is retained as sandbox scratchpad/replacement-check.txt,
not as a new library declaration. No source-library files are changed.

Change record: coord/changes/N3-retire-etale-galois-units-comparison.md.

## Proved and sorry left

Direct holes before: zero. Direct holes after: zero. Holes closed: none. Holes
added or split off: none. No decomposition is claimed.

The duplicate nonempty_equiv_galoisUnitsH2_cohomologicalBrauerGroup is retired.
Its exact proposition was proved in the sandbox from the retained source
additive equivalence, which has no sorryAx dependency.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison.

Its two public imports disappear with the duplicate module:
WeilConjectures.AlgebraicGeometry.Sites.Gm and
WeilConjectures.FieldTheory.GaloisUnitsCohomology. The source construction
continues to use these definitions; they are not globally pruned.

Its private proof imports and corresponding old proof edges are unnecessary for
this node: Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison
(lem-sc-galois-units-homogeneous-comparison) and
Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison
(lem-sc-etale-units-two-cocycle-comparison). The direct source comparison does
not pass through inhomogeneous cocycles or the pair of one-sided embeddings.
Those modules are not withdrawn in this delivery, and no claim is made that
their other consumers or dependencies are globally unnecessary.

The same node stays available to its DAG parent
lem-sc-field-brauer-comparison, including the bijection orientation it needs.
There are zero current Lean importers or applications of the retired name
outside its own file, including quarantine. No parent replacement or adaptation
is required because the mathematical comparison itself remains available.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open sorry, but this is a listed zero-hole
retirement item. The earlier keep inventory reported the differently named
source construction and transitive imports. Current inspection resolves both:
the stronger additive equivalence implies the exact former proposition, and
there are no consumers whose environments need adapting.

The old node route used two intermediate comparison modules even though the
adopted source now proves the desired result directly. The updated proof fields
follow that existing construction, preserving the unit's comparison step.
Mathlib searches through leanfinder, loogle and grep found continuous-cohomology
infrastructure and Hilbert 90, but no direct etale-units comparison; the existing
source construction is the exact replacement.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
