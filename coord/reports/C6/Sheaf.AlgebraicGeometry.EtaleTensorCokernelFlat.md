## What changed

Proved `AlgebraicGeometry.Etale.isFlat_opcycles_of_tensor_cohomology_vanishing`
in `Sheaf.AlgebraicGeometry.EtaleTensorCokernelFlat`, with its signature unchanged.
The proof uses vanishing at `a - 1`, the proved degree-zero total-tensor comparison,
and `siteSheafTensorRightIso`. Two fully proved private helpers implement the categorical
Tor diagram chase already proved in `FlatModel` and `RingedToposAcyclicKFlatPullback`,
using tensor-colimit preservation instead of monoidal closedness so that the site-object
and site-morphism universes may differ. The public imports and existing definitions stay
unchanged; all new imports are proof-only. Updated the existing node's proof and dependencies
to describe the Lean argument.

The final module compiled successfully through lcompile.py in 8.2 seconds with no warnings.
The delivery preflight checks the axioms of all three declarations.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.isFlat_opcycles_of_tensor_cohomology_vanishing`
(node `lem-kun-tor-cokernel-flat`). No holes remain in the module, and none are added.
Both new private helpers are completely proved. This is a proof, not a decomposition.

## No longer needed

Removed the proof-only import `Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion`.
The proof does not use node `lem-weil-pbc-site-flat-opcycles-tor-criterion` or its
specialized theorem: its diagonal `SmallCategory` universe requirement does not fit
`T.Etale`. The same Tor diagram chase is proved directly with the available independent-
universe tensor API. Removed this obsolete entry from the node's top-level `tool_uses`.
No other original imports were removed. No new modules or nodes are needed, and no unit
statement or unit proof step is bypassed (the unit has no recorded realized steps).

## Where the brief, the DAG or earlier work was wrong

The assigned statement is correct, including arbitrary integer `a`, the zero ring, and
zero test sheaves; the proof uses only the adjacent-degree hypotheses it needs.
The DAG's proposed direct specialization required a small-site transport not supplied by
its Lean theorem: the general criterion fixes the site object and morphism universes
both equal to the coefficient universe, whereas the small etale site has morphisms in
universe `u` and objects in `u + 1`. Rather than change any interface or select a new
site, this delivery proves the same existing categorical chase using colimit preservation.
The newer `IsFlatOnSite` hypothesis is compared with the monoidal tensor by the existing
proved `siteSheafTensorRightIso`, not by definitional equality.

The blueprint's displayed identification of Tor with the preceding tensor cohomology
should not be used without an exactness hypothesis on the original truncated sequence.
The formal proof instead proves preservation of monomorphisms by a four-refinement
chase, using exactly the stated universal tensor exactness and flatness assumptions.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
