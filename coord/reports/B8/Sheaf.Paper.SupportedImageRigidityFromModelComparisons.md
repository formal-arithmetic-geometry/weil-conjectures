## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.supported_image_rigidity_from_model_comparisons`
from the two existing stated dependencies `closed_restriction_derived_operations` and
`supported_image_mem_bounded_derived_generation`. The statement and the actual restriction
construction are unchanged. Added private, proved categorical helpers for isomorphism and
retract invariance, product closure, and filtered-complex closure. Added proof-only imports
for the two dependency modules, exact colimits of quasi-isomorphisms, and exact filtered
colimits of abelian groups.

The invertibility class is replete and triangulated by shift compatibility and triangle
two-out-of-three. Its product closure uses the original limiting cones and naturality.
For filtered diagrams, the supplied simultaneous chain model represents the restriction;
component quasi-isomorphisms remain quasi-isomorphisms under exact filtered colimits, and
the normalized invertible cocone comparisons identify this with restriction at the colimit.
The finite-model hypothesis supplies the generators, so the structural generation theorem
applies to the actual image. This is the existing DAG proof plan, without new nodes.

Searches used `msearch.py` LeanFinder for the isomorphism locus of a natural
transformation of triangulated functors (no direct closure theorem), Loogle for
`"quasiIso", "colimit"` (no hits), and grep for the generation predicate and filtered
restriction helper (no hits). Direct source searches found the existing proved
`HomologicalComplex.quasiIso` exact-colimit stability instance in
`WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim`;
the proof uses that instance rather than rebuilding filtered cohomology continuity.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.supported_image_rigidity_from_model_comparisons`
(node `lem-sfb-supported-image-rigidity-from-model-comparisons`).

No `sorry` remains in the item module. Added 0 holes and split off 0 statements.
The two existing dependency theorems remain independent proof obligations; this delivery
proves the assigned theorem from their unchanged declarations.

## No longer needed

Removed the redundant proof import `Mathlib.CategoryTheory.Triangulated.Pretriangulated`;
it is provided by the structural generation interface. No dependency nodes or modules
are pruned: all three planned proof dependencies are used.
No new obligation is introduced. The original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement or proof-plan correction was needed. In Lean, the inverse for the retract
case is written in diagrammatic composition order as
`Psi(i) ≫ inv(rho_L) ≫ Phi(p)`. The filtered argument uses the supplied simultaneous
chain model, rather than inferring a chain-level square from equality of derived components.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
